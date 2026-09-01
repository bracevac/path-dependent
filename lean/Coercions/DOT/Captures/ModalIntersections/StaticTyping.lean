import Coercions.DOT.Captures.ModalIntersections.TypingContext

/-!
# Static typing and structural adaptation

Interval realization is checked before a lexical static binder is opened.
Interval entailment is checked under the assumptions of the available
interval. Structural adaptation remains value-only; its modal case is
contravariant in requirements and checks the result under the target lock.
-/

namespace DOTCapture.ModalIntersections

namespace Interval

/-- An ambient witness realizes every present endpoint of an interval. The
proof is formed outside the interval binder, preserving no-self-discharge. -/
inductive SatisfiedBy {scope : Sig} (context : Ctx scope)
    {sort : StaticSort} (witness : StaticExpr sort scope) :
    Interval sort scope → Type where
  | unbounded :
      SatisfiedBy context witness (.bounds .none .none)
  | lower {lower : StaticExpr sort scope}
      (evidence : Includes context lower witness) :
      SatisfiedBy context witness (.bounds (.some lower) .none)
  | upper {upper : StaticExpr sort scope}
      (evidence : Includes context witness upper) :
      SatisfiedBy context witness (.bounds .none (.some upper))
  | between {lower upper : StaticExpr sort scope}
      (lowerEvidence : Includes context lower witness)
      (upperEvidence : Includes context witness upper) :
      SatisfiedBy context witness
        (.bounds (.some lower) (.some upper))

namespace SatisfiedBy

/-- Extract the lower obligation independently of the upper endpoint. -/
def lowerEvidence {scope : Sig} {context : Ctx scope}
    {sort : StaticSort} {witness lower : StaticExpr sort scope}
    {upper : Endpoint sort scope}
    (satisfaction : SatisfiedBy context witness
      (.bounds (.some lower) upper)) :
    Includes context lower witness :=
  match upper, satisfaction with
  | .none, .lower evidence => evidence
  | .some _, .between evidence _ => evidence

/-- Extract the upper obligation independently of the lower endpoint. -/
def upperEvidence {scope : Sig} {context : Ctx scope}
    {sort : StaticSort} {witness upper : StaticExpr sort scope}
    {lower : Endpoint sort scope}
    (satisfaction : SatisfiedBy context witness
      (.bounds lower (.some upper))) :
    Includes context witness upper :=
  match lower, satisfaction with
  | .none, .upper evidence => evidence
  | .some _, .between _ evidence => evidence

end SatisfiedBy

/-- Shape-preserving entailment between intervals. Every required endpoint is
derived after opening the available interval, not the required one. -/
inductive Entails {scope : Sig} (context : Ctx scope) {sort : StaticSort} :
    Interval sort scope → Interval sort scope → Type where
  | unbounded :
      Entails context (.bounds .none .none) (.bounds .none .none)
  | lower {availableLower requiredLower : StaticExpr sort scope}
      (lowerEvidence : Includes
        (context.extendStatic (.bounds (.some availableLower) .none))
        requiredLower.weaken
        (StaticExpr.bound
          (.here : BVar (scope ▹ .static sort) (.static sort)))) :
      Entails context
        (.bounds (.some availableLower) .none)
        (.bounds (.some requiredLower) .none)
  | upper {availableUpper requiredUpper : StaticExpr sort scope}
      (upperEvidence : Includes
        (context.extendStatic (.bounds .none (.some availableUpper)))
        (StaticExpr.bound
          (.here : BVar (scope ▹ .static sort) (.static sort)))
        requiredUpper.weaken) :
      Entails context
        (.bounds .none (.some availableUpper))
        (.bounds .none (.some requiredUpper))
  | between
      {availableLower availableUpper requiredLower requiredUpper :
        StaticExpr sort scope}
      (lowerEvidence : Includes
        (context.extendStatic
          (.bounds (.some availableLower) (.some availableUpper)))
        requiredLower.weaken
        (StaticExpr.bound
          (.here : BVar (scope ▹ .static sort) (.static sort))))
      (upperEvidence : Includes
        (context.extendStatic
          (.bounds (.some availableLower) (.some availableUpper)))
        (StaticExpr.bound
          (.here : BVar (scope ▹ .static sort) (.static sort)))
        requiredUpper.weaken) :
      Entails context
        (.bounds (.some availableLower) (.some availableUpper))
        (.bounds (.some requiredLower) (.some requiredUpper))

end Interval

/-- A derivation-directed, value-only structural adaptation. Logical casts
remain distinct from function, capture, quantifier, and modal structure. -/
inductive Adapts : {scope : Sig} → TypingEnv scope →
    Ty scope → Ty scope → Type where
  | identity {scope : Sig} {environment : TypingEnv scope}
      {type : Ty scope} :
      Adapts environment type type
  | cast {scope : Sig} {environment : TypingEnv scope}
      {source target : Ty scope}
      (inclusion : TypeIncludes environment.bindings source target) :
      Adapts environment source target
  | compose {scope : Sig} {environment : TypingEnv scope}
      {source middle target : Ty scope}
      (first : Adapts environment source middle)
      (second : Adapts environment middle target) :
      Adapts environment source target
  | function {scope : Sig} {environment : TypingEnv scope}
      {sourceDomain targetDomain sourceCodomain targetCodomain : Ty scope}
      (domain : Adapts environment targetDomain sourceDomain)
      (codomain : Adapts environment sourceCodomain targetCodomain) :
      Adapts environment (.arr sourceDomain sourceCodomain)
        (.arr targetDomain targetCodomain)
  | captured {scope : Sig} {environment : TypingEnv scope}
      {sourceCaptures targetCaptures : Capture scope}
      {sourceShape targetShape : Ty scope}
      (subcapture : CaptureIncludes environment.bindings
        sourceCaptures targetCaptures)
      (inner : Adapts environment sourceShape targetShape) :
      Adapts environment (.capturing sourceCaptures sourceShape)
        (.capturing targetCaptures targetShape)
  | forallI {scope : Sig} {environment : TypingEnv scope}
      {sort : StaticSort} {interval : Interval sort scope}
      {sourceBody targetBody : Ty (scope ▹ .static sort)}
      (body : Adapts (environment.extendStatic interval)
        sourceBody targetBody) :
      Adapts environment (.forallI interval sourceBody)
        (.forallI interval targetBody)
  | forallBounds {scope : Sig} {environment : TypingEnv scope}
      {sort : StaticSort}
      {sourceInterval targetInterval : Interval sort scope}
      {sourceBody targetBody : Ty (scope ▹ .static sort)}
      (bounds : Interval.Entails environment.bindings
        targetInterval sourceInterval)
      (body : Adapts (environment.extendStatic targetInterval)
        sourceBody targetBody) :
      Adapts environment (.forallI sourceInterval sourceBody)
        (.forallI targetInterval targetBody)
  | existsI {scope : Sig} {environment : TypingEnv scope}
      {sort : StaticSort} {interval : Interval sort scope}
      {sourceBody targetBody : Ty (scope ▹ .static sort)}
      (body : Adapts (environment.extendStatic interval)
        sourceBody targetBody) :
      Adapts environment (.existsI interval sourceBody)
        (.existsI interval targetBody)
  | existsBounds {scope : Sig} {environment : TypingEnv scope}
      {sort : StaticSort}
      {sourceInterval targetInterval : Interval sort scope}
      {sourceBody targetBody : Ty (scope ▹ .static sort)}
      (bounds : Interval.Entails environment.bindings
        sourceInterval targetInterval)
      (payload : Adapts (environment.extendStatic sourceInterval)
        sourceBody targetBody) :
      Adapts environment (.existsI sourceInterval sourceBody)
        (.existsI targetInterval targetBody)
  /-- Modal requirements are contravariant. The source requirements must be
  derivable using the target lock's assumptions, and the inner adapter is
  checked under that same target lock. -/
  | modal {scope : Sig} {environment : TypingEnv scope}
      {sourceSeparationCount targetSeparationCount : Nat}
      {sourceModes targetModes : List CaptureMode}
      {sourceRequirements : ModalRequirements sourceSeparationCount
        sourceModes scope}
      {targetRequirements : ModalRequirements targetSeparationCount
        targetModes scope}
      {sourceBody targetBody : Ty scope}
      (requirements : Satisfies environment.bindings
        (environment.push targetRequirements).locks sourceRequirements)
      (body : Adapts (environment.push targetRequirements)
        sourceBody targetBody) :
      Adapts environment (.modal sourceRequirements sourceBody)
        (.modal targetRequirements targetBody)

namespace Adapts

def ofIncludes {scope : Sig} {environment : TypingEnv scope}
    {source target : Ty scope}
    (inclusion : TypeIncludes environment.bindings source target) :
    Adapts environment source target :=
  .cast inclusion

def arrow {scope : Sig} {environment : TypingEnv scope}
    {sourceDomain targetDomain sourceCodomain targetCodomain : Ty scope}
    (domain : Adapts environment targetDomain sourceDomain)
    (codomain : Adapts environment sourceCodomain targetCodomain) :
    Adapts environment (.arr sourceDomain sourceCodomain)
      (.arr targetDomain targetCodomain) :=
  .function domain codomain

def captureMap {scope : Sig} {environment : TypingEnv scope}
    {capture : Capture scope} {sourceShape targetShape : Ty scope}
    (inner : Adapts environment sourceShape targetShape) :
    Adapts environment (.capturing capture sourceShape)
      (.capturing capture targetShape) :=
  .captured .refl inner

def captureWiden {scope : Sig} {environment : TypingEnv scope}
    {sourceCapture targetCapture : Capture scope} {shape : Ty scope}
    (subcapture : CaptureIncludes environment.bindings
      sourceCapture targetCapture) :
    Adapts environment (.capturing sourceCapture shape)
      (.capturing targetCapture shape) :=
  .captured subcapture .identity

end Adapts

end DOTCapture.ModalIntersections
