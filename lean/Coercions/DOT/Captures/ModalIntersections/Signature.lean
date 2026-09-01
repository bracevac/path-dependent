import Coercions.DOT.Captures.Intersections.SignatureMetatheory
import Coercions.DOT.Captures.ModalIntersections.Syntax

/-!
# Normalization of cumulative object interfaces

The existing normalization kernel is expression-parametric. This module
instantiates it with source types, captures, and classifier expressions,
retaining one member identity per label and every contributed interval or
mixed constraint.
-/

namespace DOTCapture.ModalIntersections.Interface

/-- Successful collection yields the canonical sorted representation with
nonempty entries and at most one entry per label. -/
theorem collect_normalized {scope : Sig} (interface : Interface scope)
    {signature : DOTCapture.Intersections.Signature (Expr scope)}
    (success : interface.collect = .ok signature) :
    signature.Normalized := by
  cases interface with
  | empty =>
      simp only [collect, Except.ok.injEq] at success
      subst signature
      exact DOTCapture.Intersections.Signature.empty_normalized
  | typeMember label lower upper =>
      simp only [collect, Except.ok.injEq] at success
      subst signature
      exact DOTCapture.Intersections.Signature.singletonType_normalized
        (Expr := Expr scope) label (StaticExpr.type lower)
          (StaticExpr.type upper)
  | captureMember label lower upper =>
      simp only [collect, Except.ok.injEq] at success
      subst signature
      exact DOTCapture.Intersections.Signature.singletonCapture_normalized
        (Expr := Expr scope) label (StaticExpr.capture lower)
          (StaticExpr.capture upper)
  | classifierMember label lower upper =>
      simp only [collect, Except.ok.injEq] at success
      subst signature
      exact DOTCapture.Intersections.Signature.singletonClassifier_normalized
        (Expr := Expr scope) label lower upper
  | classifierDisjoint left right =>
      simp only [collect, Except.ok.injEq] at success
      subst signature
      exact DOTCapture.Intersections.Signature.singletonConstraint_normalized
        (DOTCapture.Intersections.Constraint.classifierDisjoint
          (Expr := Expr scope) left right)
  | captureHasKind capture classifier =>
      simp only [collect, Except.ok.injEq] at success
      subst signature
      exact DOTCapture.Intersections.Signature.singletonConstraint_normalized
        (DOTCapture.Intersections.Constraint.captureHasKind
          (Expr := Expr scope) (StaticExpr.capture capture) classifier)
  | inter left right =>
      simp only [collect] at success
      cases leftResult : left.collect with
      | error conflict =>
          rw [leftResult] at success
          nomatch success
      | ok leftSignature =>
          cases rightResult : right.collect with
          | error conflict =>
              rw [leftResult, rightResult] at success
              nomatch success
          | ok rightSignature =>
              rw [leftResult, rightResult] at success
              exact DOTCapture.Intersections.Signature.merge?_normalized
                leftSignature rightSignature signature
                (collect_normalized left leftResult)
                (collect_normalized right rightResult) success
termination_by interface

/-- Collection is deterministic. -/
theorem collect_deterministic {scope : Sig} (interface : Interface scope)
    {first second : DOTCapture.Intersections.Signature (Expr scope)}
    (firstSuccess : interface.collect = .ok first)
    (secondSuccess : interface.collect = .ok second) : first = second :=
  Except.ok.inj (firstSuccess.symm.trans secondSuccess)

end DOTCapture.ModalIntersections.Interface
