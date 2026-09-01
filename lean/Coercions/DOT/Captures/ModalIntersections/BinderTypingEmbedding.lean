import Coercions.DOT.Captures.BinderOnly.Typing
import Coercions.DOT.Captures.ModalIntersections.BinderJudgmentEmbedding
import Coercions.DOT.Captures.ModalIntersections.Typing

/-!
# Typing conservativity for lexical static binders

The binder-only source embeds into the cumulative typing environment with an
empty modal-assumption stack.  This file also records that the structural
embedding commutes with source static substitution, which is the only
nontrivial index equality needed by static application and packaging.
-/

namespace DOTCapture.ModalIntersections.Embedding.BinderOnly

open DOTCapture.ModalIntersections

namespace Source

abbrev StaticSubst := DOTCapture.BinderOnly.StaticSubst

end Source

/-- A binder-only context has no active modal assumptions. -/
def typingEnvironment {scope : Sig} (sourceContext : Source.Ctx scope) :
    TypingEnv scope :=
  ⟨context sourceContext, .nil⟩

@[simp]
theorem typingEnvironment_bindings {scope : Sig}
    (sourceContext : Source.Ctx scope) :
    (typingEnvironment sourceContext).bindings = context sourceContext :=
  rfl

@[simp]
theorem typingEnvironment_locks {scope : Sig}
    (sourceContext : Source.Ctx scope) :
    (typingEnvironment sourceContext).locks = ModalAssumptions.nil :=
  rfl

@[simp]
theorem typingEnvironment_extendTerm {scope : Sig}
    (sourceContext : Source.Ctx scope) (sourceType : Source.Ty scope) :
    typingEnvironment (sourceContext.extendTerm sourceType) =
      (typingEnvironment sourceContext).extendTerm (type sourceType) :=
  rfl

@[simp]
theorem typingEnvironment_extendStatic {scope : Sig} {sort : StaticSort}
    (sourceContext : Source.Ctx scope)
    (sourceInterval : Source.Interval sort scope) :
    typingEnvironment (sourceContext.extendStatic sourceInterval) =
      (typingEnvironment sourceContext).extendStatic
        (interval sourceInterval) :=
  rfl

@[simp]
theorem typingEnvironment_extendPayload {scope : Sig} {sort : StaticSort}
    (sourceContext : Source.Ctx scope)
    (sourceInterval : Source.Interval sort scope)
    (payloadType : Source.Ty (scope ▹ .static sort)) :
    typingEnvironment
        ((sourceContext.extendStatic sourceInterval).extendTerm payloadType) =
      (typingEnvironment sourceContext).extendPayload
        (interval sourceInterval) (type payloadType) :=
  rfl

@[simp]
theorem type_weaken {scope : Sig} {kind : BinderKind}
    (sourceType : Source.Ty scope) :
    type (sourceType.weaken (kind := kind)) =
      (type sourceType).weaken (kind := kind) := by
  unfold DOTCapture.BinderOnly.Ty.weaken
    DOTCapture.ModalIntersections.Ty.weaken
  exact type_rename sourceType DOTCapture.BinderOnly.Rename.succ

@[simp]
theorem capture_weaken {scope : Sig} {kind : BinderKind}
    (sourceCapture : Source.Capture scope) :
    capture (sourceCapture.weaken (kind := kind)) =
      (capture sourceCapture).weaken (kind := kind) := by
  unfold DOTCapture.BinderOnly.Capture.weaken
    DOTCapture.ModalIntersections.Capture.weaken
  exact capture_rename sourceCapture DOTCapture.BinderOnly.Rename.succ

/-- Embed a binder-only static substitution. -/
def staticSubst {source target : Sig}
    (substitution : Source.StaticSubst source target) :
    DOTCapture.ModalIntersections.StaticSubst source target where
  termVar := substitution.termVar
  staticVar := fun index => staticExpr (substitution.staticVar index)

@[simp]
theorem staticSubst_liftTerm {source target : Sig}
    (substitution : Source.StaticSubst source target) :
    staticSubst substitution.liftTerm = (staticSubst substitution).liftTerm := by
  apply DOTCapture.ModalIntersections.StaticSubst.ext
  · intro index
    cases index <;> rfl
  · intro sort index
    cases index with
    | there index =>
        exact staticExpr_rename (substitution.staticVar index)
          DOTCapture.BinderOnly.Rename.succ

@[simp]
theorem staticSubst_liftStatic {source target : Sig}
    (substitution : Source.StaticSubst source target) (sort : StaticSort) :
    staticSubst (substitution.liftStatic sort) =
      (staticSubst substitution).liftStatic sort := by
  apply DOTCapture.ModalIntersections.StaticSubst.ext
  · intro index
    cases index with
    | there index => rfl
  · intro other index
    cases index with
    | here => cases sort <;> rfl
    | there index =>
        exact staticExpr_rename (substitution.staticVar index)
          DOTCapture.BinderOnly.Rename.succ

@[simp]
theorem staticSubst_instantiateNewest {scope : Sig} {sort : StaticSort}
    (replacement : Source.StaticExpr sort scope) :
    staticSubst
        (DOTCapture.BinderOnly.StaticSubst.instantiateNewest replacement) =
      DOTCapture.ModalIntersections.StaticSubst.instantiateNewest
        (staticExpr replacement) := by
  apply DOTCapture.ModalIntersections.StaticSubst.ext
  · intro index
    cases index with
    | there index => rfl
  · intro other index
    cases index with
    | here => rfl
    | there index =>
        exact staticRef_asExpression
          (DOTCapture.BinderOnly.StaticRef.bound index)

@[simp]
theorem staticRef_substitute {source target : Sig} {sort : StaticSort}
    (reference : Source.StaticRef sort source)
    (substitution : Source.StaticSubst source target) :
    staticExpr (reference.substitute substitution) =
      (staticRef reference).substitute (staticSubst substitution) := by
  cases reference
  rfl

mutual

@[simp]
def capture_substitute {source target : Sig}
    (sourceCapture : Source.Capture source)
    (substitution : Source.StaticSubst source target) :
    capture (sourceCapture.substitute substitution) =
      (capture sourceCapture).substitute (staticSubst substitution) :=
  match sourceCapture with
  | .empty => rfl
  | .union left right => by
      simp only [DOTCapture.BinderOnly.Capture.substitute, capture,
        DOTCapture.ModalIntersections.Capture.substitute,
        capture_substitute left substitution,
        capture_substitute right substitution]
  | .singleton receiver => rfl
  | .ref (.bound name) => by
      cases found : substitution.staticVar name with
      | capture replacement =>
          have translated := staticRef_substitute
            (DOTCapture.BinderOnly.StaticRef.bound name) substitution
          simp only [DOTCapture.BinderOnly.StaticRef.substitute, found,
            staticExpr] at translated
          simp only [DOTCapture.BinderOnly.Capture.substitute,
            DOTCapture.BinderOnly.StaticRef.substitute, found, capture,
            DOTCapture.ModalIntersections.Capture.substitute]
          rw [← translated]

@[simp]
def type_substitute {source target : Sig} (sourceType : Source.Ty source)
    (substitution : Source.StaticSubst source target) :
    type (sourceType.substitute substitution) =
      (type sourceType).substitute (staticSubst substitution) :=
  match sourceType with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .ref (.bound name) => by
      cases found : substitution.staticVar name with
      | type replacement =>
          have translated := staticRef_substitute
            (DOTCapture.BinderOnly.StaticRef.bound name) substitution
          simp only [DOTCapture.BinderOnly.StaticRef.substitute, found,
            staticExpr] at translated
          simp only [DOTCapture.BinderOnly.Ty.substitute,
            DOTCapture.BinderOnly.StaticRef.substitute, found, type,
            DOTCapture.ModalIntersections.Ty.substitute]
          rw [← translated]
  | .capturing captures shape => by
      simp only [DOTCapture.BinderOnly.Ty.substitute, type,
        DOTCapture.ModalIntersections.Ty.substitute,
        capture_substitute captures substitution,
        type_substitute shape substitution]
  | .arr domain codomain => by
      simp only [DOTCapture.BinderOnly.Ty.substitute, type,
        DOTCapture.ModalIntersections.Ty.substitute,
        type_substitute domain substitution,
        type_substitute codomain substitution]
  | .forallI sourceInterval body => by
      simp only [DOTCapture.BinderOnly.Ty.substitute, type,
        DOTCapture.ModalIntersections.Ty.substitute,
        interval_substitute sourceInterval substitution,
        type_substitute body (substitution.liftStatic _),
        staticSubst_liftStatic]
  | .existsI sourceInterval body => by
      simp only [DOTCapture.BinderOnly.Ty.substitute, type,
        DOTCapture.ModalIntersections.Ty.substitute,
        interval_substitute sourceInterval substitution,
        type_substitute body (substitution.liftStatic _),
        staticSubst_liftStatic]

@[simp]
def staticExpr_substitute {source target : Sig} {sort : StaticSort}
    (expression : Source.StaticExpr sort source)
    (substitution : Source.StaticSubst source target) :
    staticExpr (expression.substitute substitution) =
      (staticExpr expression).substitute (staticSubst substitution) :=
  match expression with
  | .type sourceType => by
      simp only [DOTCapture.BinderOnly.StaticExpr.substitute, staticExpr,
        DOTCapture.ModalIntersections.StaticExpr.substitute,
        type_substitute sourceType substitution]
  | .capture sourceCapture => by
      simp only [DOTCapture.BinderOnly.StaticExpr.substitute, staticExpr,
        DOTCapture.ModalIntersections.StaticExpr.substitute,
        capture_substitute sourceCapture substitution]

@[simp]
def endpoint_substitute {source target : Sig} {sort : StaticSort}
    (sourceEndpoint : Source.Endpoint sort source)
    (substitution : Source.StaticSubst source target) :
    endpoint (sourceEndpoint.substitute substitution) =
      (endpoint sourceEndpoint).substitute (staticSubst substitution) :=
  match sourceEndpoint with
  | .none => rfl
  | .some expression => by
      simp only [DOTCapture.BinderOnly.Endpoint.substitute, endpoint,
        DOTCapture.ModalIntersections.Endpoint.substitute,
        staticExpr_substitute expression substitution]

@[simp]
def interval_substitute {source target : Sig} {sort : StaticSort}
    (sourceInterval : Source.Interval sort source)
    (substitution : Source.StaticSubst source target) :
    interval (sourceInterval.substitute substitution) =
      (interval sourceInterval).substitute (staticSubst substitution) :=
  match sourceInterval with
  | .bounds lower upper => by
      simp only [DOTCapture.BinderOnly.Interval.substitute, interval,
        DOTCapture.ModalIntersections.Interval.substitute,
        endpoint_substitute lower substitution,
        endpoint_substitute upper substitution]

end

@[simp]
theorem type_instantiateStatic {scope : Sig} {sort : StaticSort}
    (sourceType : Source.Ty (scope ▹ .static sort))
    (replacement : Source.StaticExpr sort scope) :
    type (sourceType.instantiateStatic replacement) =
      (type sourceType).instantiateStatic (staticExpr replacement) := by
  unfold DOTCapture.BinderOnly.Ty.instantiateStatic
    DOTCapture.ModalIntersections.Ty.instantiateStatic
  rw [type_substitute, staticSubst_instantiateNewest]

@[simp]
theorem staticExpr_bound {scope : Sig} {sort : StaticSort}
    (name : BVar scope (.static sort)) :
    staticExpr (DOTCapture.BinderOnly.StaticExpr.bound name) =
      DOTCapture.ModalIntersections.StaticExpr.bound name :=
  staticRef_asExpression (DOTCapture.BinderOnly.StaticRef.bound name)

/-! ## Static premises and adapters -/

/-- Every binder-only interval realization remains valid in the embedded
ordinary context. -/
def intervalSatisfiedBy {scope : Sig} {sourceContext : Source.Ctx scope}
    {sort : StaticSort} {witness : Source.StaticExpr sort scope}
    {sourceInterval : Source.Interval sort scope}
    (satisfaction : DOTCapture.BinderOnly.Interval.SatisfiedBy
      sourceContext witness sourceInterval) :
    DOTCapture.ModalIntersections.Interval.SatisfiedBy
      (context sourceContext) (staticExpr witness)
      (interval sourceInterval) :=
  match satisfaction with
  | .unbounded => .unbounded
  | .lower evidence => .lower (includes evidence)
  | .upper evidence => .upper (includes evidence)
  | .between lowerEvidence upperEvidence =>
      .between (includes lowerEvidence) (includes upperEvidence)

/-- Shape-preserving interval entailment embeds without changing which
hypothetical interval supplies the endpoint assumptions. -/
def intervalEntails {scope : Sig} {sourceContext : Source.Ctx scope}
    {sort : StaticSort}
    {available required : Source.Interval sort scope}
    (entailment : DOTCapture.BinderOnly.Interval.Entails sourceContext
      available required) :
    DOTCapture.ModalIntersections.Interval.Entails (context sourceContext)
      (interval available) (interval required) :=
  match entailment with
  | .unbounded => .unbounded
  | .lower lowerEvidence => by
      apply DOTCapture.ModalIntersections.Interval.Entails.lower
      simpa only [context_extendStatic, interval, endpoint,
        DOTCapture.BinderOnly.StaticExpr.weaken,
        DOTCapture.ModalIntersections.StaticExpr.weaken,
        staticExpr_rename, staticExpr_bound] using includes lowerEvidence
  | .upper upperEvidence => by
      apply DOTCapture.ModalIntersections.Interval.Entails.upper
      simpa only [context_extendStatic, interval, endpoint,
        DOTCapture.BinderOnly.StaticExpr.weaken,
        DOTCapture.ModalIntersections.StaticExpr.weaken,
        staticExpr_rename, staticExpr_bound] using includes upperEvidence
  | .between lowerEvidence upperEvidence => by
      apply DOTCapture.ModalIntersections.Interval.Entails.between
      · simpa only [context_extendStatic, interval, endpoint,
          DOTCapture.BinderOnly.StaticExpr.weaken,
          DOTCapture.ModalIntersections.StaticExpr.weaken,
          staticExpr_rename, staticExpr_bound] using
          includes lowerEvidence
      · simpa only [context_extendStatic, interval, endpoint,
          DOTCapture.BinderOnly.StaticExpr.weaken,
          DOTCapture.ModalIntersections.StaticExpr.weaken,
          staticExpr_rename, staticExpr_bound] using
          includes upperEvidence

/-- Binder-only types never embed as the cumulative object shape reserved
for stable object binders. -/
theorem type_plain {scope : Sig} (sourceType : Source.Ty scope) :
    Plain (type sourceType) := by
  cases sourceType with
  | capturing _ shape => cases shape <;> trivial
  | top | bot | one | ref | arr | forallI | existsI => trivial

/-- Every binder-only structural adapter embeds under the empty-lock typing
environment. -/
def adapts {scope : Sig} {sourceContext : Source.Ctx scope}
    {source target : Source.Ty scope}
    (adapter : DOTCapture.BinderOnly.Adapts sourceContext source target) :
    DOTCapture.ModalIntersections.Adapts (typingEnvironment sourceContext)
      (type source) (type target) :=
  match adapter with
  | .identity => .identity
  | .cast inclusion => .cast (typeIncludes inclusion)
  | .compose first second => .compose (adapts first) (adapts second)
  | .function domain codomain =>
      .function (adapts domain) (adapts codomain)
  | .captured subcapture inner =>
      .captured (captureIncludes subcapture) (adapts inner)
  | .forallI body => .forallI (adapts body)
  | .forallBounds bounds body =>
      .forallBounds (intervalEntails bounds) (adapts body)
  | .existsI body => .existsI (adapts body)
  | .existsBounds bounds payload =>
      .existsBounds (intervalEntails bounds) (adapts payload)

/-! ## Value and computation typing -/

mutual

/-- Embed a binder-only value-typing derivation. -/
def valueHasType {scope : Sig} {sourceContext : Source.Ctx scope}
    {sourceValue : Source.Value scope} {sourceType : Source.Ty scope}
    (typing : DOTCapture.BinderOnly.Value.HasType sourceContext sourceValue
      sourceType) :
    DOTCapture.ModalIntersections.Value.HasType
      (typingEnvironment sourceContext) (value sourceValue)
      (type sourceType) :=
  match typing with
  | .var => by
      simpa only [typingEnvironment, context_lookupTerm, type_precise] using
        (DOTCapture.ModalIntersections.Value.HasType.var
          (environment := typingEnvironment sourceContext))
  | .unit => .unit
  | @DOTCapture.BinderOnly.Value.HasType.lam _ _ domain codomain _ _ _
      bodyTyping captures => by
      apply DOTCapture.ModalIntersections.Value.HasType.lam
        (type_plain domain)
      · simpa only [typingEnvironment_extendTerm, type_weaken] using
          termHasType bodyTyping
      · simpa only [TypingEnv.extendTerm_bindings,
          typingEnvironment_bindings, context_extendTerm, capture,
          path, capture_weaken] using captureIncludes captures
  | .staticLam bodyTyping captures => by
      apply DOTCapture.ModalIntersections.Value.HasType.staticLam
      · simpa only [typingEnvironment_extendStatic] using
          valueHasType bodyTyping
      · simpa only [TypingEnv.extendStatic_bindings,
          context_extendStatic, type_outerCapture, capture_weaken] using
          captureIncludes captures
  | .pack satisfaction payloadTyping captures => by
      apply DOTCapture.ModalIntersections.Value.HasType.pack
        (intervalSatisfiedBy satisfaction)
      · simpa only [type_instantiateStatic] using
          valueHasType payloadTyping
      · simpa only [type_instantiateStatic, type_outerCapture] using
          captureIncludes captures
  | .adapt sourceTyping adapter =>
      .adapt (valueHasType sourceTyping) (adapts adapter)

/-- Embed a binder-only value-MNF computation into the cumulative
computation category.  Returned operands make `Capture.seq` definitionally
collapse to the original immediate-use indices. -/
def termHasType {scope : Sig} {sourceContext : Source.Ctx scope}
    {sourceTerm : Source.Term scope} {sourceUse : Source.Capture scope}
    {sourceType : Source.Ty scope}
    (typing : DOTCapture.BinderOnly.Term.HasType sourceContext sourceTerm
      sourceUse sourceType) :
    DOTCapture.ModalIntersections.Term.HasType
      (typingEnvironment sourceContext) (term sourceTerm)
      (capture sourceUse) (type sourceType) :=
  match typing with
  | .ret sourceTyping => .ret (valueHasType sourceTyping)
  | .app functionTyping functionShape argumentTyping => by
      have embeddedShape := congrArg type functionShape
      simp only [type_stripCapture, type] at embeddedShape
      simpa only [term, capture, type_outerCapture, Capture.seq_empty] using
        (DOTCapture.ModalIntersections.Term.HasType.app
          (.ret (valueHasType functionTyping)) embeddedShape
          (type_plain _)
          (.ret (valueHasType argumentTyping)))
  | @DOTCapture.BinderOnly.Term.HasType.let' _ _ result bound _ _ _ _ _
      rhsTyping bodyTyping discharge => by
      apply DOTCapture.ModalIntersections.Term.HasType.letPlain
        (type_plain bound) (termHasType rhsTyping)
      · simpa only [typingEnvironment_extendTerm, type_weaken] using
          termHasType bodyTyping
      · simpa only [TypingEnv.extendTerm_bindings,
          typingEnvironment_bindings, context_extendTerm,
          capture_weaken] using captureIncludes discharge
  | .staticApp functionTyping functionShape satisfaction => by
      have embeddedShape := congrArg type functionShape
      simp only [type_stripCapture, type] at embeddedShape
      simpa only [term, capture, type_outerCapture, Capture.seq_empty,
          type_instantiateStatic] using
        (DOTCapture.ModalIntersections.Term.HasType.staticApp
          (.ret (valueHasType functionTyping)) embeddedShape
          (intervalSatisfiedBy satisfaction))
  | @DOTCapture.BinderOnly.Term.HasType.«open» _ _ sort sourceInterval
      payloadType result package body packageType bodyUse bodyOuterUse
      packageTyping packageShape bodyTyping discharge => by
      have embeddedShape := congrArg type packageShape
      simp only [type_stripCapture, type] at embeddedShape
      have embeddedBody := termHasType bodyTyping
      have typedBody :
          DOTCapture.ModalIntersections.Term.HasType
            ((typingEnvironment sourceContext).extendPayload
              (interval sourceInterval) (type payloadType))
            (term body) (capture bodyUse)
            (((type result).weaken (kind := .static sort)).weaken
              (kind := .term)) := by
        simpa only [typingEnvironment_extendPayload, type_weaken] using
          embeddedBody
      have embeddedDischarge := captureIncludes discharge
      have typedDischarge :
          CaptureIncludes
            ((typingEnvironment sourceContext).extendPayload
              (interval sourceInterval) (type payloadType)).bindings
            (capture bodyUse)
            (.union
              (((capture bodyOuterUse).weaken
                (kind := .static sort)).weaken (kind := .term))
              (.singleton (.var .here))) := by
        simpa only [TypingEnv.extendPayload_bindings,
          typingEnvironment_bindings, context_extendStatic,
          context_extendTerm, capture, path, capture_weaken] using
          embeddedDischarge
      simpa only [term, capture, type_outerCapture, Capture.seq_empty] using
        (DOTCapture.ModalIntersections.Term.HasType.«open»
          (.ret (valueHasType packageTyping)) embeddedShape typedBody
          typedDischarge)
  | .use sourceTyping inclusion =>
      .use (termHasType sourceTyping) (captureIncludes inclusion)

end

end DOTCapture.ModalIntersections.Embedding.BinderOnly
