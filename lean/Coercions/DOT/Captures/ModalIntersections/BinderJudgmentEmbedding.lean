import Coercions.DOT.Captures.BinderOnly.StaticJudgments
import Coercions.DOT.Captures.ModalIntersections.ContextEmbedding
import Coercions.DOT.Captures.ModalIntersections.StaticJudgments

/-!
# Embedding binder-only static judgments

Lexical interval lookup and every binder-only inclusion constructor embed into
the cumulative proof-relevant judgments.  The construction preserves the
structurally embedded endpoint expressions in its result indices.
-/

namespace DOTCapture.ModalIntersections.Embedding.BinderOnly

open DOTCapture.ModalIntersections

/-- Embed a lexical lower-bound lookup certificate. -/
def hasLower {scope : Sig} {sourceContext : Source.Ctx scope}
    {sort : StaticSort} {reference : Source.StaticRef sort scope}
    {endpoint : Source.StaticExpr sort scope}
    (bound : DOTCapture.BinderOnly.HasLower
      sourceContext reference endpoint) :
    DOTCapture.ModalIntersections.HasLower (context sourceContext)
      (staticRef reference) (staticExpr endpoint) :=
  match bound with
  | .bound found => by
      apply DOTCapture.ModalIntersections.HasLower.bound
      have translated := congrArg interval found
      simpa only [context_lookupStatic, interval,
        DOTCapture.ModalIntersections.Embedding.BinderOnly.endpoint,
        staticExpr] using translated

/-- Embed a lexical upper-bound lookup certificate. -/
def hasUpper {scope : Sig} {sourceContext : Source.Ctx scope}
    {sort : StaticSort} {reference : Source.StaticRef sort scope}
    {endpoint : Source.StaticExpr sort scope}
    (bound : DOTCapture.BinderOnly.HasUpper
      sourceContext reference endpoint) :
    DOTCapture.ModalIntersections.HasUpper (context sourceContext)
      (staticRef reference) (staticExpr endpoint) :=
  match bound with
  | .bound found => by
      apply DOTCapture.ModalIntersections.HasUpper.bound
      have translated := congrArg interval found
      simpa only [context_lookupStatic, interval,
        DOTCapture.ModalIntersections.Embedding.BinderOnly.endpoint,
        staticExpr] using translated

/-- Embed every binder-only directed inclusion derivation. -/
def includes {scope : Sig} {sourceContext : Source.Ctx scope}
    {sort : StaticSort} {source target : Source.StaticExpr sort scope}
    (proof : DOTCapture.BinderOnly.Includes sourceContext source target) :
    DOTCapture.ModalIntersections.Includes (context sourceContext)
      (staticExpr source) (staticExpr target) :=
  match proof with
  | .refl => .refl
  | .trans first second => .trans (includes first) (includes second)
  | .lower bound => by
      simpa only [DOTCapture.BinderOnly.StaticRef.expression_eq_asExpression,
        DOTCapture.ModalIntersections.StaticRef.expression_eq_asExpression,
        staticRef_asExpression] using
        DOTCapture.ModalIntersections.Includes.lower (hasLower bound)
  | .upper bound => by
      simpa only [DOTCapture.BinderOnly.StaticRef.expression_eq_asExpression,
        DOTCapture.ModalIntersections.StaticRef.expression_eq_asExpression,
        staticRef_asExpression] using
        DOTCapture.ModalIntersections.Includes.upper (hasUpper bound)
  | .typeTop => .typeTop
  | .typeBottom => .typeBottom
  | .typeArrow domain codomain =>
      .typeArrow (includes domain) (includes codomain)
  | .typeCapturing captures shape =>
      .typeCapturing (includes captures) (includes shape)
  | .captureEmpty => .captureEmpty
  | .captureUnionLeft => .captureUnionLeft
  | .captureUnionRight => .captureUnionRight
  | .captureUnionElim fromLeft fromRight =>
      .captureUnionElim (includes fromLeft) (includes fromRight)
  | .captureVariable found => by
      apply DOTCapture.ModalIntersections.Includes.captureVariable
      have translated := congrArg type found
      simpa only [context_lookupTerm, type, capture] using translated

/-- Type-specialized binder-only inclusion embeds at the translated types. -/
def typeIncludes {scope : Sig} {sourceContext : Source.Ctx scope}
    {source target : Source.Ty scope}
    (proof : DOTCapture.BinderOnly.TypeIncludes sourceContext source target) :
    DOTCapture.ModalIntersections.TypeIncludes (context sourceContext)
      (type source) (type target) :=
  includes proof

/-- Capture-specialized binder-only inclusion embeds at the translated
captures. -/
def captureIncludes {scope : Sig} {sourceContext : Source.Ctx scope}
    {source target : Source.Capture scope}
    (proof : DOTCapture.BinderOnly.CaptureIncludes
      sourceContext source target) :
    DOTCapture.ModalIntersections.CaptureIncludes (context sourceContext)
      (capture source) (capture target) :=
  includes proof

end DOTCapture.ModalIntersections.Embedding.BinderOnly
