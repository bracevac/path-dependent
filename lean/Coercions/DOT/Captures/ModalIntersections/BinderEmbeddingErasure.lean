import Coercions.DOT.Captures.ModalIntersections.BinderEmbedding
import Coercions.DOT.Captures.ModalIntersections.Erasure
import Coercions.Translation.ManySorted.BinderOnly.SourceErasure

/-!
# Exact erasure of the binder-only embedding

The binder-only and cumulative languages share their heterogeneous scope and
runtime variable conventions.  Embedding therefore preserves direct source
erasure literally, for any projection of heterogeneous term variables into a
runtime scope.  Static abstractions and applications disappear, packages
erase to their payloads, and opening becomes the same single runtime `let` on
both sides.

This module relates the two independently defined erasures.  It does not use a
target compiler or add an umbrella import.
-/

namespace DOTCapture.ModalIntersections.Erasure.BinderOnly

namespace Source

abbrev Value := DOTCapture.BinderOnly.Value
abbrev Term := DOTCapture.BinderOnly.Term

end Source

namespace Embedding

export DOTCapture.ModalIntersections.Embedding.BinderOnly (value term)

end Embedding

namespace OldErasure

export DOTCaptureToManySortedFC.BinderOnly.SourceErasure
  (Renaming eraseValueWith eraseTermWith compiledRenaming eraseValue eraseTerm)

end OldErasure

open DOTCapture.ModalIntersections

/-! ## Shared runtime-renaming structure -/

@[simp]
theorem liftTerm_eq {scope : Sig} {runtimeScope : Nat}
    (rho : OldErasure.Renaming scope runtimeScope) :
    Renaming.liftTerm rho =
      DOTCaptureToManySortedFC.BinderOnly.SourceErasure.Renaming.liftTerm rho :=
  rfl

@[simp]
theorem liftStatic_eq {scope : Sig} {runtimeScope : Nat}
    (rho : OldErasure.Renaming scope runtimeScope) (sort : StaticSort) :
    Renaming.liftStatic rho sort =
      DOTCaptureToManySortedFC.BinderOnly.SourceErasure.Renaming.liftStatic
        rho sort := rfl

@[simp]
theorem liftPayload_eq {scope : Sig} {runtimeScope : Nat}
    (rho : OldErasure.Renaming scope runtimeScope) (sort : StaticSort) :
    Renaming.liftPayload rho sort =
      DOTCaptureToManySortedFC.BinderOnly.SourceErasure.Renaming.liftPayload
        rho sort := rfl

/-! ## Arbitrary heterogeneous-renaming theorem -/

mutual

/-- Embedding a binder-only value preserves its independently defined erasure
under every heterogeneous-to-runtime variable projection. -/
@[simp]
def eraseValueWith_embedding {scope : Sig} {runtimeScope : Nat}
    (rho : OldErasure.Renaming scope runtimeScope)
    (sourceValue : Source.Value scope) :
    eraseValueWith rho (Embedding.value sourceValue) =
      OldErasure.eraseValueWith rho sourceValue :=
  match sourceValue with
  | .var _ => rfl
  | .unit => rfl
  | .lam _ _ body => by
      simp only [Embedding.value, eraseValueWith,
        OldErasure.eraseValueWith]
      exact congrArg (fun erasedBody =>
          (.lam erasedBody : Runtime.Tm runtimeScope))
        (eraseTermWith_embedding
          (DOTCaptureToManySortedFC.BinderOnly.SourceErasure.Renaming.liftTerm
            rho)
          body)
  | @DOTCapture.BinderOnly.Value.staticLam _ sort _ body => by
      simp only [Embedding.value, eraseValueWith,
        OldErasure.eraseValueWith]
      exact eraseValueWith_embedding
        (DOTCaptureToManySortedFC.BinderOnly.SourceErasure.Renaming.liftStatic
          rho sort)
        body
  | .pack _ _ _ payload => by
      simp only [Embedding.value, eraseValueWith,
        OldErasure.eraseValueWith]
      exact eraseValueWith_embedding rho payload

/-- Computation counterpart of `eraseValueWith_embedding`.  In particular,
the embedded value-restricted application and static eliminations introduce
no administrative runtime binding. -/
@[simp]
def eraseTermWith_embedding {scope : Sig} {runtimeScope : Nat}
    (rho : OldErasure.Renaming scope runtimeScope)
    (sourceTerm : Source.Term scope) :
    eraseTermWith rho (Embedding.term sourceTerm) =
      OldErasure.eraseTermWith rho sourceTerm :=
  match sourceTerm with
  | .ret sourceValue => by
      simp only [Embedding.term, eraseTermWith,
        OldErasure.eraseTermWith,
        eraseValueWith_embedding rho sourceValue]
  | .app function argument => by
      simp only [Embedding.term, eraseTermWith,
        OldErasure.eraseTermWith,
        eraseValueWith_embedding rho function,
        eraseValueWith_embedding rho argument]
  | .let' _ rhs body => by
      simp only [Embedding.term, eraseTermWith,
        OldErasure.eraseTermWith, eraseTermWith_embedding rho rhs]
      exact congrArg (fun erasedBody =>
          (.let' (OldErasure.eraseTermWith rho rhs) erasedBody :
            Runtime.Tm runtimeScope))
        (eraseTermWith_embedding
          (DOTCaptureToManySortedFC.BinderOnly.SourceErasure.Renaming.liftTerm
            rho)
          body)
  | .staticApp _ function _ => by
      simp only [Embedding.term, eraseTermWith,
        OldErasure.eraseTermWith,
        eraseValueWith_embedding rho function]
  | @DOTCapture.BinderOnly.Term.«open» _ sort _ _ _ package body => by
      simp only [Embedding.term, eraseTermWith,
        OldErasure.eraseTermWith,
        eraseValueWith_embedding rho package]
      exact congrArg (fun erasedBody =>
          (.let' (OldErasure.eraseValueWith rho package) erasedBody :
            Runtime.Tm runtimeScope))
        (eraseTermWith_embedding
          (DOTCaptureToManySortedFC.BinderOnly.SourceErasure.Renaming.liftPayload
            rho sort)
          body)

end

/-! ## Context and canonical specializations -/

/-- Exact preservation using the runtime projection computed from an arbitrary
binder-only source context. -/
@[simp]
theorem eraseValue_context_embedding {scope : Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (sourceValue : Source.Value scope) :
    eraseValueWith (OldErasure.compiledRenaming context)
        (Embedding.value sourceValue) =
      OldErasure.eraseValue context sourceValue := by
  simpa only [OldErasure.eraseValue] using
    eraseValueWith_embedding (OldErasure.compiledRenaming context) sourceValue

/-- Computation counterpart of `eraseValue_context_embedding`. -/
@[simp]
theorem eraseTerm_context_embedding {scope : Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (sourceTerm : Source.Term scope) :
    eraseTermWith (OldErasure.compiledRenaming context)
        (Embedding.term sourceTerm) =
      OldErasure.eraseTerm context sourceTerm := by
  simpa only [OldErasure.eraseTerm] using
    eraseTermWith_embedding (OldErasure.compiledRenaming context) sourceTerm

/-- On an all-term scope, cumulative canonical erasure is exactly binder-only
erasure under the context-free identity projection. -/
@[simp]
theorem eraseValue_embedding {scope : Nat}
    (sourceValue : Source.Value (termScope scope)) :
    eraseValue (Embedding.value sourceValue) =
      OldErasure.eraseValueWith Renaming.allTermIdentity sourceValue := by
  simpa only [eraseValue] using
    eraseValueWith_embedding Renaming.allTermIdentity sourceValue

/-- Computation counterpart of `eraseValue_embedding`. -/
@[simp]
theorem eraseTerm_embedding {scope : Nat}
    (sourceTerm : Source.Term (termScope scope)) :
    eraseTerm (Embedding.term sourceTerm) =
      OldErasure.eraseTermWith Renaming.allTermIdentity sourceTerm := by
  simpa only [eraseTerm] using
    eraseTermWith_embedding Renaming.allTermIdentity sourceTerm

end DOTCapture.ModalIntersections.Erasure.BinderOnly
