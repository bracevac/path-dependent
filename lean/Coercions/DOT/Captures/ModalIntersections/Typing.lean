import Coercions.DOT.Captures.ModalIntersections.Substitution
import Coercions.DOT.Captures.ModalIntersections.StaticTyping
import Coercions.DOT.Captures.ModalIntersections.ObjectJudgments

/-!
# Computational typing for modal captured intersections

These four mutually recursive judgments combine the general-expression
captured-DOT rules with lexical static abstraction, existential packaging,
and access-only modal suspension.  Values retain capabilities in the outer
capture of their type; computations separately report the capabilities used
while they run.

Ordinary binders remain restricted to non-object shapes.  Object consumers
and object lets preserve the negative/positive split: positive objects are
existential values, while a canonical literal or an already-open stable path
may be supplied directly to a negative consumer.  Static application,
existential opening, ordinary application, and modal unlocking all accept
arbitrary computations and charge them in source evaluation order.
-/

namespace DOTCapture.ModalIntersections

mutual

/-- Declarative typing of cumulative values.  Structural adapters are
deliberately value-only. -/
inductive Value.HasType : {scope : Sig} -> TypingEnv scope ->
    Value scope -> Ty scope -> Type where
  | var {scope : Sig} {environment : TypingEnv scope}
      {name : BVar scope .term} :
      Value.HasType environment (.var name)
        ((environment.bindings.lookupTerm name).precise (.var name))
  | unit {scope : Sig} {environment : TypingEnv scope} :
      Value.HasType environment .unit .one
  | lam {scope : Sig} {environment : TypingEnv scope}
      {domain codomain : Ty scope} {body : Term (scope ▹ .term)}
      {bodyUse : Capture (scope ▹ .term)} {closure : Capture scope}
      (domainPlain : Plain domain)
      (bodyTyping : Term.HasType (environment.extendTerm domain) body
        bodyUse (codomain.weaken (kind := .term)))
      (captures : CaptureIncludes
        (environment.extendTerm domain).bindings bodyUse
        (.union (closure.weaken (kind := .term))
          (.singleton (.var .here)))) :
      Value.HasType environment (.lam domain codomain body)
        (.capturing closure (.arr domain codomain))
  | staticLam {scope : Sig} {environment : TypingEnv scope}
      {sort : StaticSort} {interval : Interval sort scope}
      {body : Value (scope ▹ .static sort)}
      {bodyType : Ty (scope ▹ .static sort)}
      {closure : Capture scope}
      (bodyTyping : Value.HasType (environment.extendStatic interval)
        body bodyType)
      (captures : CaptureIncludes
        (environment.extendStatic interval).bindings bodyType.outerCapture
        (closure.weaken (kind := .static sort))) :
      Value.HasType environment (.staticLam interval body)
        (.capturing closure (.forallI interval bodyType))
  | pack {scope : Sig} {environment : TypingEnv scope}
      {sort : StaticSort} {interval : Interval sort scope}
      {payloadType : Ty (scope ▹ .static sort)}
      {witness : StaticExpr sort scope} {payload : Value scope}
      {closure : Capture scope}
      (satisfaction : Interval.SatisfiedBy environment.bindings witness
        interval)
      (payloadTyping : Value.HasType environment payload
        (payloadType.instantiateStatic witness))
      (captures : CaptureIncludes environment.bindings
        (payloadType.instantiateStatic witness).outerCapture closure) :
      Value.HasType environment
        (.pack interval payloadType witness payload)
        (.capturing closure (.existsI interval payloadType))
  /-- A modal value checks its suspended body with the advertised frame
  active.  The frame is not available to code outside the suspension. -/
  | lock {scope : Sig} {environment : TypingEnv scope}
      {separationCount : Nat} {modes : List CaptureMode}
      {requirements : ModalRequirements separationCount modes scope}
      {result : Ty scope} {closure bodyUse : Capture scope}
      {body : Term scope}
      (bodyTyping : Term.HasType (environment.push requirements) body
        bodyUse result)
      (captures : CaptureIncludes environment.bindings bodyUse closure) :
      Value.HasType environment
        (.lock requirements result closure body)
        (.capturing closure (.modal requirements result))
  | objectConsumer {scope : Sig} {environment : TypingEnv scope}
      {parameter : ObjectType scope} {resultTemplate : Ty scope}
      {body : Term (scope ▹ .term)}
      {bodyUse : Capture (scope ▹ .term)} {closure : Capture scope}
      (bodyTyping : Term.HasType
        (environment.extendTerm parameter.formedType) body bodyUse
        ((resultTemplate.weaken (kind := .term)).openAt (.var .here)))
      (captures : CaptureIncludes
        (environment.extendTerm parameter.formedType).bindings bodyUse
        (.union (closure.weaken (kind := .term))
          (.singleton (.var .here)))) :
      Value.HasType environment
        (.objectConsumer parameter resultTemplate body)
        (.capturing closure (.objectArrow parameter resultTemplate))
  /-- Legacy typing of the same object-consumer syntax at an ambient ordinary
  arrow.  This is retained only for the cumulative M11 embedding. -/
  | legacyObjectConsumer {scope : Sig} {environment : TypingEnv scope}
      {parameter : ObjectType scope} {result : Ty scope}
      {body : Term (scope ▹ .term)}
      {bodyUse : Capture (scope ▹ .term)} {closure : Capture scope}
      (bodyTyping : Term.HasType
        (environment.extendTerm parameter.formedType) body bodyUse
        (result.weaken (kind := .term)))
      (captures : CaptureIncludes
        (environment.extendTerm parameter.formedType).bindings bodyUse
        (.union (closure.weaken (kind := .term))
          (.singleton (.var .here)))) :
      Value.HasType environment (.objectConsumer parameter result body)
        (.capturing closure (.arr parameter.formedType result))
  /-- Legacy negative introduction through an ordinary lambda, retained for
  the structural M10 embedding. -/
  | embeddedObjectConsumer {scope : Sig} {environment : TypingEnv scope}
      {parameter : ObjectType scope} {result : Ty scope}
      {body : Term (scope ▹ .term)}
      {bodyUse : Capture (scope ▹ .term)} {closure : Capture scope}
      (bodyTyping : Term.HasType
        (environment.extendTerm parameter.formedType) body bodyUse
        (result.weaken (kind := .term)))
      (captures : CaptureIncludes
        (environment.extendTerm parameter.formedType).bindings bodyUse
        (.union (closure.weaken (kind := .term))
          (.singleton (.var .here)))) :
      Value.HasType environment (.lam parameter.formedType result body)
        (.capturing closure (.arr parameter.formedType result))
  | object {scope : Sig} {environment : TypingEnv scope}
      {object : ObjectType scope} {payload : Value scope}
      {payloadType : Ty scope}
      (realization : ObjectType.Realization environment.bindings object)
      (payloadTyping : Value.HasType environment payload payloadType)
      (payloadShape : TypeIncludes environment.bindings
        payloadType.stripCapture
        (ObjectType.realizedRepresentation object
          realization.model).stripCapture)
      (payloadCapture : CaptureIncludes environment.bindings
        payloadType.outerCapture
        (ObjectType.realizedRepresentation object
          realization.model).outerCapture)
      (objectCapture : CaptureIncludes environment.bindings
        (ObjectType.realizedRepresentation object
          realization.model).outerCapture object.outerCapture) :
      Value.HasType environment (.object object payload) object.formedType
  | adapt {scope : Sig} {environment : TypingEnv scope}
      {value : Value scope} {source target : Ty scope}
      (valueTyping : Value.HasType environment value source)
      (adapter : Adapts environment source target) :
      Value.HasType environment value target

/-- Canonical or stable negative object arguments.  Arbitrary computations
must first be opened by an explicit `objectLet`. -/
inductive ObjectArgument.HasType : {scope : Sig} -> TypingEnv scope ->
    Term scope -> ObjectType scope -> LocalModel.Model scope -> Type where
  | literal {scope : Sig} {environment : TypingEnv scope}
      {available expected : ObjectType scope} {payload : Value scope}
      {payloadType : Ty scope}
      (realization : ObjectType.Realization environment.bindings available)
      (payloadTyping : Value.HasType environment payload payloadType)
      (payloadShape : TypeIncludes environment.bindings
        payloadType.stripCapture
        (ObjectType.realizedRepresentation available
          realization.model).stripCapture)
      (payloadCapture : CaptureIncludes environment.bindings
        payloadType.outerCapture
        (ObjectType.realizedRepresentation available
          realization.model).outerCapture)
      (objectCapture : CaptureIncludes environment.bindings
        (ObjectType.realizedRepresentation available
          realization.model).outerCapture available.outerCapture)
      (adaptation : ObjectType.Adapts environment.bindings available expected)
      (representation : TypeIncludes environment.bindings
        (ObjectType.realizedRepresentation available realization.model)
        (ObjectType.realizedRepresentation expected
          (adaptation.mapping.apply realization.model)))
      (expectedCapture : CaptureIncludes environment.bindings
        (ObjectType.realizedRepresentation expected
          (adaptation.mapping.apply realization.model)).outerCapture
        expected.outerCapture) :
      ObjectArgument.HasType environment
        (.ret (.object available payload)) expected
        (adaptation.mapping.apply realization.model)
  | stable {scope : Sig} {environment : TypingEnv scope}
      {name : BVar scope .term} {available expected : ObjectType scope}
      (canonical : environment.bindings.lookupTerm name =
        available.formedType)
      (adaptation : ObjectType.Adapts environment.bindings available expected)
      (representation : TypeIncludes environment.bindings
        (ObjectType.realizedRepresentation available
          (LocalModel.atPath (.var name)))
        (ObjectType.realizedRepresentation expected
          (adaptation.mapping.apply (LocalModel.atPath (.var name)))))
      (expectedCapture : CaptureIncludes environment.bindings
        (ObjectType.realizedRepresentation expected
          (adaptation.mapping.apply (LocalModel.atPath (.var name)))).outerCapture
        expected.outerCapture) :
      ObjectArgument.HasType environment (.ret (.var name)) expected
        (adaptation.mapping.apply (LocalModel.atPath (.var name)))

/-- Legacy evidence for a computation producing an ambient ordinary arrow
that consumes an object.  Native dependent consumers are typed directly at
`Ty.objectArrow` and need no syntax-directed function sub-judgment. -/
inductive ObjectFunction.HasType : {scope : Sig} -> TypingEnv scope ->
    Term scope -> Capture scope -> ObjectType scope -> Ty scope ->
      Capture scope -> Type where
  | returned {scope : Sig} {environment : TypingEnv scope}
      {parameter : ObjectType scope} {result : Ty scope}
      {body : Term (scope ▹ .term)}
      {bodyUse : Capture (scope ▹ .term)} {closure : Capture scope}
      (bodyTyping : Term.HasType
        (environment.extendTerm parameter.formedType) body bodyUse
        (result.weaken (kind := .term)))
      (captures : CaptureIncludes
        (environment.extendTerm parameter.formedType).bindings bodyUse
        (.union (closure.weaken (kind := .term))
          (.singleton (.var .here)))) :
      ObjectFunction.HasType environment
        (.ret (.objectConsumer parameter result body)) .empty
        parameter result closure
  | embeddedReturned {scope : Sig} {environment : TypingEnv scope}
      {parameter : ObjectType scope} {result : Ty scope}
      {body : Term (scope ▹ .term)}
      {bodyUse : Capture (scope ▹ .term)} {closure : Capture scope}
      (bodyTyping : Term.HasType
        (environment.extendTerm parameter.formedType) body bodyUse
        (result.weaken (kind := .term)))
      (captures : CaptureIncludes
        (environment.extendTerm parameter.formedType).bindings bodyUse
        (.union (closure.weaken (kind := .term))
          (.singleton (.var .here)))) :
      ObjectFunction.HasType environment
        (.ret (.lam parameter.formedType result body)) .empty
        parameter result closure
  | letPlain {scope : Sig} {environment : TypingEnv scope}
      {parameter : ObjectType scope} {result bound : Ty scope}
      {closure : Capture scope} {rhs : Term scope}
      {body : Term (scope ▹ .term)} {rhsUse : Capture scope}
      {bodyUse : Capture (scope ▹ .term)} {bodyOuterUse : Capture scope}
      (boundPlain : Plain bound)
      (rhsTyping : Term.HasType environment rhs rhsUse bound)
      (bodyTyping : ObjectFunction.HasType (environment.extendTerm bound) body
        bodyUse (parameter.weaken (kind := .term))
        (result.weaken (kind := .term))
        (closure.weaken (kind := .term)))
      (discharge : CaptureIncludes
        (environment.extendTerm bound).bindings bodyUse
        (bodyOuterUse.weaken (kind := .term))) :
      ObjectFunction.HasType environment
        (.let' (.capturing closure (.arr parameter.formedType result))
          rhs body)
        (.union rhsUse bodyOuterUse) parameter result closure
  | use {scope : Sig} {environment : TypingEnv scope}
      {function : Term scope} {sourceUse targetUse : Capture scope}
      {parameter : ObjectType scope} {result : Ty scope}
      {closure : Capture scope}
      (functionTyping : ObjectFunction.HasType environment function sourceUse
        parameter result closure)
      (inclusion : CaptureIncludes environment.bindings sourceUse targetUse) :
      ObjectFunction.HasType environment function targetUse
        parameter result closure

/-- Declarative typing of cumulative computations.  The capture index is an
upper bound on capabilities used immediately by the computation. -/
inductive Term.HasType : {scope : Sig} -> TypingEnv scope -> Term scope ->
    Capture scope -> Ty scope -> Type where
  | ret {scope : Sig} {environment : TypingEnv scope}
      {value : Value scope} {type : Ty scope}
      (valueTyping : Value.HasType environment value type) :
      Term.HasType environment (.ret value) .empty type
  | select {scope : Sig} {environment : TypingEnv scope}
      {receiver : Path scope} {object : ObjectType scope}
      (exposes : ExposesObject environment.bindings receiver object) :
      Term.HasType environment (.select receiver .payload)
        (.singleton receiver) (object.representationAt receiver)
  | app {scope : Sig} {environment : TypingEnv scope}
      {function argument : Term scope}
      {functionUse argumentUse : Capture scope}
      {functionType domain codomain : Ty scope}
      (functionTyping : Term.HasType environment function functionUse
        functionType)
      (functionShape : functionType.stripCapture = .arr domain codomain)
      (domainPlain : Plain domain)
      (argumentTyping : Term.HasType environment argument argumentUse domain) :
      Term.HasType environment (.app function argument)
        (functionUse.seq
          (argumentUse.seq
            (.union functionType.outerCapture domain.outerCapture))) codomain
  | staticApp {scope : Sig} {environment : TypingEnv scope}
      {sort : StaticSort} {interval : Interval sort scope}
      {function : Term scope} {argument : StaticExpr sort scope}
      {functionUse : Capture scope} {functionType : Ty scope}
      {bodyType : Ty (scope ▹ .static sort)}
      (functionTyping : Term.HasType environment function functionUse
        functionType)
      (functionShape : functionType.stripCapture =
        .forallI interval bodyType)
      (satisfaction : Interval.SatisfiedBy environment.bindings argument
        interval) :
      Term.HasType environment (.staticApp interval function argument)
        (functionUse.seq functionType.outerCapture)
        (bodyType.instantiateStatic argument)
  | «open» {scope : Sig} {environment : TypingEnv scope}
      {sort : StaticSort} {interval : Interval sort scope}
      {payloadType : Ty (scope ▹ .static sort)} {result : Ty scope}
      {package : Term scope} {body : Term (PayloadScope scope sort)}
      {packageUse : Capture scope} {packageType : Ty scope}
      {bodyUse : Capture (PayloadScope scope sort)}
      {bodyOuterUse : Capture scope}
      (packageTyping : Term.HasType environment package packageUse packageType)
      (packageShape : packageType.stripCapture =
        .existsI interval payloadType)
      (bodyTyping : Term.HasType
        (environment.extendPayload interval payloadType) body bodyUse
        ((result.weaken (kind := .static sort)).weaken (kind := .term)))
      (discharge : CaptureIncludes
        (environment.extendPayload interval payloadType).bindings bodyUse
        (.union
          ((bodyOuterUse.weaken (kind := .static sort)).weaken
            (kind := .term))
          (.singleton (.var .here)))) :
      Term.HasType environment
        (.«open» interval payloadType result package body)
        (packageUse.seq (.union packageType.outerCapture bodyOuterUse)) result
  /-- Unlocking checks the advertised requirements only in the ambient lock
  stack, then charges evaluation of the scrutinee followed by the retained
  closure of the produced modal value. -/
  | unlock {scope : Sig} {environment : TypingEnv scope}
      {separationCount : Nat} {modes : List CaptureMode}
      {requirements : ModalRequirements separationCount modes scope}
      {scrutinee : Term scope} {scrutineeUse : Capture scope}
      {scrutineeType result : Ty scope}
      (scrutineeTyping : Term.HasType environment scrutinee scrutineeUse
        scrutineeType)
      (scrutineeShape : scrutineeType.stripCapture =
        .modal requirements result)
      (satisfaction : Satisfies environment.bindings environment.locks
        requirements) :
      Term.HasType environment (.unlock requirements scrutinee)
        (scrutineeUse.seq scrutineeType.outerCapture) result
  | objectApp {scope : Sig} {environment : TypingEnv scope}
      {parameter : ObjectType scope} {function argument : Term scope}
      {functionUse : Capture scope} {functionType resultTemplate : Ty scope}
      {argumentModel : LocalModel.Model scope}
      (functionTyping : Term.HasType environment function functionUse
        functionType)
      (functionShape : functionType.stripCapture =
        .objectArrow parameter resultTemplate)
      (argumentTyping : ObjectArgument.HasType environment argument parameter
        argumentModel) :
      Term.HasType environment (.objectApp parameter function argument)
        (functionUse.seq
          (.union functionType.outerCapture parameter.outerCapture))
        (resultTemplate.realizeLocals argumentModel)
  /-- Legacy object application at an ambient ordinary arrow, retained by the
  native-syntax M11 embedding. -/
  | legacyObjectApp {scope : Sig} {environment : TypingEnv scope}
      {parameter : ObjectType scope} {function argument : Term scope}
      {functionUse closure : Capture scope} {result : Ty scope}
      {argumentModel : LocalModel.Model scope}
      (functionTyping : ObjectFunction.HasType environment function
        functionUse parameter result closure)
      (argumentTyping : ObjectArgument.HasType environment argument parameter
        argumentModel) :
      Term.HasType environment (.objectApp parameter function argument)
        (functionUse.seq (.union closure parameter.outerCapture)) result
  /-- Legacy ordinary application retained by the M10 embedding. -/
  | embeddedObjectApp {scope : Sig} {environment : TypingEnv scope}
      {parameter : ObjectType scope} {function argument : Term scope}
      {functionUse closure : Capture scope} {result : Ty scope}
      {argumentModel : LocalModel.Model scope}
      (functionTyping : ObjectFunction.HasType environment function
        functionUse parameter result closure)
      (argumentTyping : ObjectArgument.HasType environment argument parameter
        argumentModel) :
      Term.HasType environment (.app function argument)
        (functionUse.seq (.union closure parameter.outerCapture)) result
  | letPlain {scope : Sig} {environment : TypingEnv scope}
      {result bound : Ty scope} {rhs : Term scope}
      {body : Term (scope ▹ .term)} {rhsUse : Capture scope}
      {bodyUse : Capture (scope ▹ .term)} {bodyOuterUse : Capture scope}
      (boundPlain : Plain bound)
      (rhsTyping : Term.HasType environment rhs rhsUse bound)
      (bodyTyping : Term.HasType (environment.extendTerm bound) body bodyUse
        (result.weaken (kind := .term)))
      (discharge : CaptureIncludes
        (environment.extendTerm bound).bindings bodyUse
        (bodyOuterUse.weaken (kind := .term))) :
      Term.HasType environment (.let' result rhs body)
        (.union rhsUse bodyOuterUse) result
  | objectLet {scope : Sig} {environment : TypingEnv scope}
      {object : ObjectType scope} {result : Ty scope}
      {rhs : Term scope} {rhsUse : Capture scope}
      {body : Term (scope ▹ .term)}
      {bodyUse : Capture (scope ▹ .term)} {bodyOuterUse : Capture scope}
      (rhsTyping : Term.HasType environment rhs rhsUse object.formedType)
      (bodyTyping : Term.HasType
        (environment.extendTerm object.formedType) body bodyUse
        (result.weaken (kind := .term)))
      (discharge : CaptureIncludes
        (environment.extendTerm object.formedType).bindings bodyUse
        (.union (bodyOuterUse.weaken (kind := .term))
          (.singleton (.var .here)))) :
      Term.HasType environment (.objectLet object result rhs body)
        (rhsUse.seq (.union object.outerCapture bodyOuterUse)) result
  /-- Legacy source let retained by the structural M10/M11 embeddings. -/
  | embeddedObjectLet {scope : Sig} {environment : TypingEnv scope}
      {object : ObjectType scope} {result : Ty scope}
      {rhs : Term scope} {rhsUse : Capture scope}
      {body : Term (scope ▹ .term)}
      {bodyUse : Capture (scope ▹ .term)} {bodyOuterUse : Capture scope}
      (rhsTyping : Term.HasType environment rhs rhsUse object.formedType)
      (bodyTyping : Term.HasType
        (environment.extendTerm object.formedType) body bodyUse
        (result.weaken (kind := .term)))
      (discharge : CaptureIncludes
        (environment.extendTerm object.formedType).bindings bodyUse
        (.union (bodyOuterUse.weaken (kind := .term))
          (.singleton (.var .here)))) :
      Term.HasType environment (.let' result rhs body)
        (rhsUse.seq (.union object.outerCapture bodyOuterUse)) result
  | use {scope : Sig} {environment : TypingEnv scope}
      {term : Term scope} {sourceUse targetUse : Capture scope}
      {type : Ty scope}
      (termTyping : Term.HasType environment term sourceUse type)
      (inclusion : CaptureIncludes environment.bindings sourceUse targetUse) :
      Term.HasType environment term targetUse type

end

namespace Value.HasType

/-- Recover the declared type of a variable.  A captured declaration first
receives the native precise singleton capture and is then widened through the
context's variable-capture fact; all other type shapes are definitionally
unchanged by precision. -/
def declaredVar {scope : Sig} {environment : TypingEnv scope}
    {name : BVar scope .term} :
    Value.HasType environment (.var name)
      (environment.bindings.lookupTerm name) := by
  cases found : environment.bindings.lookupTerm name with
  | top => simpa [Ty.precise, found] using
      (Value.HasType.var (environment := environment) (name := name))
  | bot => simpa [Ty.precise, found] using
      (Value.HasType.var (environment := environment) (name := name))
  | one => simpa [Ty.precise, found] using
      (Value.HasType.var (environment := environment) (name := name))
  | ref reference => simpa [Ty.precise, found] using
      (Value.HasType.var (environment := environment) (name := name))
  | arr domain codomain => simpa [Ty.precise, found] using
      (Value.HasType.var (environment := environment) (name := name))
  | objectArrow parameter resultTemplate => simpa [Ty.precise, found] using
      (Value.HasType.var (environment := environment) (name := name))
  | capturing captures shape =>
      exact .adapt
        (by simpa [Ty.precise, found] using
          (Value.HasType.var (environment := environment) (name := name)))
        (.captured (.captureVariable found) .identity)
  | forallI interval body => simpa [Ty.precise, found] using
      (Value.HasType.var (environment := environment) (name := name))
  | existsI interval body => simpa [Ty.precise, found] using
      (Value.HasType.var (environment := environment) (name := name))
  | modal requirements body => simpa [Ty.precise, found] using
      (Value.HasType.var (environment := environment) (name := name))
  | object object => simpa [Ty.precise, found] using
      (Value.HasType.var (environment := environment) (name := name))

end Value.HasType

namespace ObjectArgument.HasType

/-- Realize a dependent result template at the exact model exposed by a
negative-use object argument.  The model is an output index of the judgment,
so this operation neither reruns nor reinterprets the argument. -/
def realizeResult {scope : Sig} {environment : TypingEnv scope}
    {argument : Term scope} {object : ObjectType scope}
    {model : LocalModel.Model scope}
    (_typing : ObjectArgument.HasType environment argument object model)
    (resultTemplate : Ty scope) : Ty scope :=
  resultTemplate.realizeLocals model

/-- Recover the ordinary positive typing of a canonical literal argument. -/
def literalValueTyping {scope : Sig} {environment : TypingEnv scope}
    {available : ObjectType scope} {payload : Value scope}
    {payloadType : Ty scope}
    (realization : ObjectType.Realization environment.bindings available)
    (payloadTyping : Value.HasType environment payload payloadType)
    (payloadShape : TypeIncludes environment.bindings
      payloadType.stripCapture
      (ObjectType.realizedRepresentation available
        realization.model).stripCapture)
    (payloadCapture : CaptureIncludes environment.bindings
      payloadType.outerCapture
      (ObjectType.realizedRepresentation available
        realization.model).outerCapture)
    (objectCapture : CaptureIncludes environment.bindings
      (ObjectType.realizedRepresentation available
        realization.model).outerCapture available.outerCapture) :
    Value.HasType environment (.object available payload) available.formedType :=
  .object realization payloadTyping payloadShape payloadCapture objectCapture

end ObjectArgument.HasType

namespace ObjectFunction.HasType

/-- Forget the negative-use witness and recover ordinary typing at the
corresponding captured arrow. -/
def toTermTyping {scope : Sig} {environment : TypingEnv scope}
    {function : Term scope} {use : Capture scope}
    {parameter : ObjectType scope} {result : Ty scope}
    {closure : Capture scope}
    (typing : ObjectFunction.HasType environment function use parameter result
      closure) :
    Term.HasType environment function use
      (.capturing closure (.arr parameter.formedType result)) :=
  match typing with
  | .returned bodyTyping captures =>
      .ret (.legacyObjectConsumer bodyTyping captures)
  | .embeddedReturned bodyTyping captures =>
      .ret (.embeddedObjectConsumer bodyTyping captures)
  | @ObjectFunction.HasType.letPlain scope environment parameter result bound
      closure rhs body rhsUse bodyUse bodyOuterUse boundPlain rhsTyping
      bodyTyping discharge => by
      have bodyOrdinary :
          Term.HasType (environment.extendTerm bound) body bodyUse
            ((Ty.capturing closure
              (Ty.arr parameter.formedType result)).weaken
                (kind := .term)) := by
        simpa [ObjectType.weaken, Ty.weaken] using toTermTyping bodyTyping
      exact .letPlain boundPlain rhsTyping bodyOrdinary discharge
  | .use functionTyping inclusion =>
      .use (toTermTyping functionTyping) inclusion

end ObjectFunction.HasType

namespace ExposesObject

/-- A stable payload selection may contract its receiver root to the
capture retained by the opened representation. -/
def payload {scope : Sig} {environment : TypingEnv scope}
    {receiver : Path scope} {object : ObjectType scope}
    (exposes : ExposesObject environment.bindings receiver object) :
    Term.HasType environment (.select receiver .payload)
      (object.representationAt receiver).outerCapture
      (object.representationAt receiver) :=
  .use (.select exposes) (.payloadRoot exposes)

end ExposesObject

end DOTCapture.ModalIntersections
