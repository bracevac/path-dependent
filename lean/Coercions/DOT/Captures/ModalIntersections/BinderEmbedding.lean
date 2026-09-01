import Coercions.DOT.Captures.BinderOnly.Term
import Coercions.DOT.Captures.ModalIntersections.Term

/-!
# Embedding lexical static binders into modal captured intersections

The binder-only source already uses the heterogeneous scope algebra reused by
the cumulative language.  Its static syntax therefore embeds structurally,
without translating scopes or variables.  Its value-restricted eliminands are
returned into the cumulative computation category; those `ret` nodes disappear
when the cumulative compiler elaborates a returned value.
-/

namespace DOTCapture.ModalIntersections.Embedding.BinderOnly

open DOTCapture.ModalIntersections

namespace Source

abbrev Path := DOTCapture.BinderOnly.Path
abbrev StaticRef := DOTCapture.BinderOnly.StaticRef
abbrev Capture := DOTCapture.BinderOnly.Capture
abbrev Ty := DOTCapture.BinderOnly.Ty
abbrev StaticExpr := DOTCapture.BinderOnly.StaticExpr
abbrev Endpoint := DOTCapture.BinderOnly.Endpoint
abbrev Interval := DOTCapture.BinderOnly.Interval
abbrev Value := DOTCapture.BinderOnly.Value
abbrev Term := DOTCapture.BinderOnly.Term

end Source

/-- Both source layers use the same hidden-static-then-payload scope. -/
@[simp]
theorem payloadScope_eq (scope : Sig) (sort : StaticSort) :
    DOTCapture.BinderOnly.PayloadScope scope sort =
      DOTCapture.ModalIntersections.PayloadScope scope sort := rfl

/-- Embed a variable-only stable path. -/
def path {scope : Sig} : Source.Path scope -> Path scope
  | .var name => .var name

/-- Embed a lexically bound static reference. -/
def staticRef {scope : Sig} {sort : StaticSort} :
    Source.StaticRef sort scope -> StaticRef sort scope
  | .bound name => .bound name

mutual

/-- Embed a capture expression. -/
def capture {scope : Sig} : Source.Capture scope -> Capture scope
  | .empty => .empty
  | .union left right => .union (capture left) (capture right)
  | .singleton receiver => .singleton (path receiver)
  | .ref reference => .ref (staticRef reference)

/-- Embed a binder-only type, retaining every lexical interval. -/
def type {scope : Sig} : Source.Ty scope -> Ty scope
  | .top => .top
  | .bot => .bot
  | .one => .one
  | .ref reference => .ref (staticRef reference)
  | .capturing captures shape => .capturing (capture captures) (type shape)
  | .arr domain codomain => .arr (type domain) (type codomain)
  | .forallI sourceInterval body =>
      .forallI (interval sourceInterval) (type body)
  | .existsI sourceInterval body =>
      .existsI (interval sourceInterval) (type body)

/-- Embed a sorted static expression. -/
def staticExpr {scope : Sig} {sort : StaticSort} :
    Source.StaticExpr sort scope -> StaticExpr sort scope
  | .type sourceType => .type (type sourceType)
  | .capture sourceCapture => .capture (capture sourceCapture)

/-- Embed one optional interval endpoint. -/
def endpoint {scope : Sig} {sort : StaticSort} :
    Source.Endpoint sort scope -> Endpoint sort scope
  | .none => .none
  | .some expression => .some (staticExpr expression)

/-- Embed a true interval without changing endpoint order or presence. -/
def interval {scope : Sig} {sort : StaticSort} :
    Source.Interval sort scope -> Interval sort scope
  | .bounds lower upper => .bounds (endpoint lower) (endpoint upper)

end

mutual

/-- Embed every binder-only value. -/
def value {scope : Sig} : Source.Value scope -> Value scope
  | .var name => .var name
  | .unit => .unit
  | .lam domain codomain body =>
      .lam (type domain) (type codomain) (term body)
  | .staticLam sourceInterval body =>
      .staticLam (interval sourceInterval) (value body)
  | .pack sourceInterval payloadType witness payload =>
      .pack (interval sourceInterval) (type payloadType)
        (staticExpr witness) (value payload)

/-- Embed every binder-only computation.

Old application and static eliminations consume values.  The cumulative
constructors consume computations, so an embedded value is returned directly;
no administrative runtime binding is introduced. -/
def term {scope : Sig} : Source.Term scope -> Term scope
  | .ret sourceValue => .ret (value sourceValue)
  | .app function argument =>
      .app (.ret (value function)) (.ret (value argument))
  | .let' result rhs body =>
      .let' (type result) (term rhs) (term body)
  | .staticApp sourceInterval function argument =>
      .staticApp (interval sourceInterval) (.ret (value function))
        (staticExpr argument)
  | .«open» sourceInterval payloadType result package body =>
      .«open» (interval sourceInterval) (type payloadType) (type result)
        (.ret (value package)) (term body)

end

/-! ## Naturality under heterogeneous renaming -/

@[simp]
theorem path_rename {source target : Sig} (sourcePath : Source.Path source)
    (rho : Rename source target) :
    path (sourcePath.rename rho) = (path sourcePath).rename rho := by
  cases sourcePath
  rfl

@[simp]
theorem staticRef_rename {source target : Sig} {sort : StaticSort}
    (reference : Source.StaticRef sort source) (rho : Rename source target) :
    staticRef (reference.rename rho) = (staticRef reference).rename rho := by
  cases reference
  rfl

mutual

@[simp]
def capture_rename {source target : Sig}
    (sourceCapture : Source.Capture source) (rho : Rename source target) :
    capture (sourceCapture.rename rho) =
      (capture sourceCapture).rename rho :=
  match sourceCapture with
  | .empty => rfl
  | .union left right => by
      simp only [DOTCapture.BinderOnly.Capture.rename, capture,
        DOTCapture.ModalIntersections.Capture.rename,
        capture_rename left, capture_rename right]
  | .singleton receiver => by
      simp only [DOTCapture.BinderOnly.Capture.rename, capture,
        DOTCapture.ModalIntersections.Capture.rename, path_rename]
  | .ref reference => by
      simp only [DOTCapture.BinderOnly.Capture.rename, capture,
        DOTCapture.ModalIntersections.Capture.rename, staticRef_rename]

@[simp]
def type_rename {source target : Sig} (sourceType : Source.Ty source)
    (rho : Rename source target) :
    type (sourceType.rename rho) = (type sourceType).rename rho :=
  match sourceType with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .ref reference => by
      simp only [DOTCapture.BinderOnly.Ty.rename, type,
        DOTCapture.ModalIntersections.Ty.rename, staticRef_rename]
  | .capturing captures shape => by
      simp only [DOTCapture.BinderOnly.Ty.rename, type,
        DOTCapture.ModalIntersections.Ty.rename, capture_rename captures,
        type_rename shape]
  | .arr domain codomain => by
      simp only [DOTCapture.BinderOnly.Ty.rename, type,
        DOTCapture.ModalIntersections.Ty.rename, type_rename domain,
        type_rename codomain]
  | .forallI sourceInterval body => by
      simp only [DOTCapture.BinderOnly.Ty.rename, type,
        DOTCapture.ModalIntersections.Ty.rename, interval_rename sourceInterval,
        type_rename body]
  | .existsI sourceInterval body => by
      simp only [DOTCapture.BinderOnly.Ty.rename, type,
        DOTCapture.ModalIntersections.Ty.rename, interval_rename sourceInterval,
        type_rename body]

@[simp]
def staticExpr_rename {source target : Sig} {sort : StaticSort}
    (expression : Source.StaticExpr sort source) (rho : Rename source target) :
    staticExpr (expression.rename rho) =
      (staticExpr expression).rename rho :=
  match expression with
  | .type sourceType => by
      simp only [DOTCapture.BinderOnly.StaticExpr.rename, staticExpr,
        DOTCapture.ModalIntersections.StaticExpr.rename,
        type_rename sourceType]
  | .capture sourceCapture => by
      simp only [DOTCapture.BinderOnly.StaticExpr.rename, staticExpr,
        DOTCapture.ModalIntersections.StaticExpr.rename,
        capture_rename sourceCapture]

@[simp]
def endpoint_rename {source target : Sig} {sort : StaticSort}
    (sourceEndpoint : Source.Endpoint sort source) (rho : Rename source target) :
    endpoint (sourceEndpoint.rename rho) =
      (endpoint sourceEndpoint).rename rho :=
  match sourceEndpoint with
  | .none => rfl
  | .some expression => by
      simp only [DOTCapture.BinderOnly.Endpoint.rename, endpoint,
        DOTCapture.ModalIntersections.Endpoint.rename,
        staticExpr_rename expression]

@[simp]
def interval_rename {source target : Sig} {sort : StaticSort}
    (sourceInterval : Source.Interval sort source) (rho : Rename source target) :
    interval (sourceInterval.rename rho) =
      (interval sourceInterval).rename rho :=
  match sourceInterval with
  | .bounds lower upper => by
      simp only [DOTCapture.BinderOnly.Interval.rename, interval,
        DOTCapture.ModalIntersections.Interval.rename,
        endpoint_rename lower, endpoint_rename upper]

end


mutual

@[simp]
def value_rename {source target : Sig} (sourceValue : Source.Value source)
    (rho : Rename source target) :
    value (sourceValue.rename rho) = (value sourceValue).rename rho :=
  match sourceValue with
  | .var _ => rfl
  | .unit => rfl
  | .lam domain codomain body => by
      simp only [DOTCapture.BinderOnly.Value.rename, value,
        DOTCapture.ModalIntersections.Value.rename, type_rename domain,
        type_rename codomain, term_rename body]
  | .staticLam sourceInterval body => by
      simp only [DOTCapture.BinderOnly.Value.rename, value,
        DOTCapture.ModalIntersections.Value.rename,
        interval_rename sourceInterval, value_rename body]
  | .pack sourceInterval payloadType witness payload => by
      simp only [DOTCapture.BinderOnly.Value.rename, value,
        DOTCapture.ModalIntersections.Value.rename,
        interval_rename sourceInterval, type_rename payloadType,
        staticExpr_rename witness, value_rename payload]

@[simp]
def term_rename {source target : Sig} (sourceTerm : Source.Term source)
    (rho : Rename source target) :
    term (sourceTerm.rename rho) = (term sourceTerm).rename rho :=
  match sourceTerm with
  | .ret sourceValue => by
      simp only [DOTCapture.BinderOnly.Term.rename, term,
        DOTCapture.ModalIntersections.Term.rename, value_rename sourceValue]
  | .app function argument => by
      simp only [DOTCapture.BinderOnly.Term.rename, term,
        DOTCapture.ModalIntersections.Term.rename, value_rename function,
        value_rename argument]
  | .let' result rhs body => by
      simp only [DOTCapture.BinderOnly.Term.rename, term,
        DOTCapture.ModalIntersections.Term.rename, type_rename result,
        term_rename rhs, term_rename body]
  | .staticApp sourceInterval function argument => by
      simp only [DOTCapture.BinderOnly.Term.rename, term,
        DOTCapture.ModalIntersections.Term.rename,
        interval_rename sourceInterval, value_rename function,
        staticExpr_rename argument]
  | @DOTCapture.BinderOnly.Term.«open» _ sort sourceInterval payloadType
      result package body => by
      simp only [DOTCapture.BinderOnly.Term.rename, term,
        DOTCapture.ModalIntersections.Term.rename,
        interval_rename sourceInterval, type_rename payloadType,
        type_rename result, value_rename package]
      congr 1
      simpa [DOTCapture.BinderOnly.Rename.liftPayload,
        DOTCapture.ModalIntersections.Rename.liftPayload] using
        term_rename body
          (DOTCapture.BinderOnly.Rename.liftPayload rho sort)

end

/-! ## Interaction with capture-predictive type projections -/

@[simp]
theorem type_outerCapture {scope : Sig} (sourceType : Source.Ty scope) :
    capture sourceType.outerCapture = (type sourceType).outerCapture := by
  cases sourceType <;> rfl

@[simp]
theorem type_stripCapture {scope : Sig} (sourceType : Source.Ty scope) :
    type sourceType.stripCapture = (type sourceType).stripCapture := by
  cases sourceType <;> rfl

@[simp]
theorem type_precise {scope : Sig} (sourceType : Source.Ty scope)
    (sourcePath : Source.Path scope) :
    type (sourceType.precise sourcePath) =
      (type sourceType).precise (path sourcePath) := by
  cases sourceType <;> rfl

@[simp]
theorem staticRef_asExpression {scope : Sig} {sort : StaticSort}
    (reference : Source.StaticRef sort scope) :
    staticExpr reference.asExpression = (staticRef reference).asExpression := by
  cases reference
  cases sort <;> rfl

end DOTCapture.ModalIntersections.Embedding.BinderOnly
