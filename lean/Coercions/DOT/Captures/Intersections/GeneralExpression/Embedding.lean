import Coercions.DOT.Captures.Acyclic.GeneralExpression.Erasure
import Coercions.DOT.Captures.Intersections.GeneralExpression.Erasure

/-!
# Embedding the M10 general-expression language

The embedding is structural on the computational language and uses the
existing conservative embedding of M10 static syntax into labeled
intersection syntax.  M10's two construction witnesses are inputs to its
typing/model-realization judgment; the generalized raw object literal records
the resulting source `ObjectType` and its one runtime payload.  No target
artifact is introduced here.
-/

namespace DOTCapture.Intersections.GeneralExpression.Embedding

namespace M10

abbrev Value := DOTCapture.Acyclic.GeneralExpression.Value
abbrev Term := DOTCapture.Acyclic.GeneralExpression.Term

end M10

open DOTCapture.Intersections.GeneralExpression

mutual

/-- Embed an M10 value, translating all static annotations. -/
def embedValue {scope : Scope} : M10.Value scope -> Value scope
  | .var name => .var name
  | .unit => .unit
  | .lam domain codomain body =>
      .lam (DOTCapture.Intersections.Source.embedM10Ty domain)
        (DOTCapture.Intersections.Source.embedM10Ty codomain)
        (embedTerm body)
  | .object signature _typeWitness _captureWitness payload =>
      .object (DOTCapture.Intersections.Source.embedM10ObjectType signature)
        (embedValue payload)

/-- Embed an M10 computation without inserting administrative terms. -/
def embedTerm {scope : Scope} : M10.Term scope -> Term scope
  | .ret value => .ret (embedValue value)
  | .select receiver .v =>
      .select (DOTCapture.Intersections.Source.embedM10Path receiver) .payload
  | .app function argument => .app (embedTerm function) (embedTerm argument)
  | .let' result rhs body =>
      .let' (DOTCapture.Intersections.Source.embedM10Ty result)
        (embedTerm rhs) (embedTerm body)

end

@[simp]
theorem erasePathWith_embed {scope runtimeScope : Nat}
    (rho : Erasure.Renaming scope runtimeScope)
    (path : DOTCapture.Acyclic.Path scope) :
    Erasure.erasePathWith rho
        (DOTCapture.Intersections.Source.embedM10Path path) =
      DOTCapture.Acyclic.GeneralExpression.Erasure.erasePathWith rho path := by
  cases path
  rfl

/-- The two independently defined erasure renamings lift identically. -/
theorem lift_eq_m10 {source target : Nat}
    (rho : Erasure.Renaming source target) :
    Erasure.Renaming.lift rho =
      DOTCapture.Acyclic.GeneralExpression.Erasure.Renaming.lift rho := by
  funext name
  cases name <;> rfl

mutual

/-- Embedding preserves runtime code for every ambient runtime renaming. -/
@[simp]
theorem eraseValueWith_embed {scope runtimeScope : Nat}
    (rho : Erasure.Renaming scope runtimeScope) (value : M10.Value scope) :
    Erasure.eraseValueWith rho (embedValue value) =
      DOTCapture.Acyclic.GeneralExpression.Erasure.eraseValueWith rho value := by
  cases value with
  | var name => rfl
  | unit => rfl
  | lam domain codomain body =>
      simp only [embedValue, Erasure.eraseValueWith,
        DOTCapture.Acyclic.GeneralExpression.Erasure.eraseValueWith]
      rw [eraseTermWith_embed]
      rw [lift_eq_m10]
  | object signature typeWitness captureWitness payload =>
      simp only [embedValue, Erasure.eraseValueWith,
        DOTCapture.Acyclic.GeneralExpression.Erasure.eraseValueWith]
      exact eraseValueWith_embed rho payload

/-- Embedding preserves the complete runtime computation literally. -/
@[simp]
theorem eraseTermWith_embed {scope runtimeScope : Nat}
    (rho : Erasure.Renaming scope runtimeScope) (term : M10.Term scope) :
    Erasure.eraseTermWith rho (embedTerm term) =
      DOTCapture.Acyclic.GeneralExpression.Erasure.eraseTermWith rho term := by
  cases term with
  | ret value =>
      simp only [embedTerm, Erasure.eraseTermWith,
        DOTCapture.Acyclic.GeneralExpression.Erasure.eraseTermWith]
      exact eraseValueWith_embed rho value
  | select receiver label =>
      cases label
      simp only [embedTerm, Erasure.eraseTermWith,
        DOTCapture.Acyclic.GeneralExpression.Erasure.eraseTermWith]
      rw [erasePathWith_embed]
  | app function argument =>
      simp only [embedTerm, Erasure.eraseTermWith,
        DOTCapture.Acyclic.GeneralExpression.Erasure.eraseTermWith]
      rw [eraseTermWith_embed, eraseTermWith_embed]
  | let' result rhs body =>
      simp only [embedTerm, Erasure.eraseTermWith,
        DOTCapture.Acyclic.GeneralExpression.Erasure.eraseTermWith]
      rw [eraseTermWith_embed, eraseTermWith_embed, lift_eq_m10]

end

/-- Canonical runtime renamings also coincide. -/
theorem identity_eq_m10 {scope : Nat} :
    (@Erasure.Renaming.identity scope) =
      (@DOTCapture.Acyclic.GeneralExpression.Erasure.Renaming.identity scope) := by
  funext name
  induction name with
  | here => rfl
  | there name ih =>
      simp only [Erasure.Renaming.identity_there,
        DOTCapture.Acyclic.GeneralExpression.Erasure.Renaming.identity_there,
        ih]

/-- Closed or open M10 values have exactly the same canonical erasure after
embedding. -/
@[simp]
theorem eraseValue_embed {scope : Nat} (value : M10.Value scope) :
    Erasure.eraseValue (embedValue value) =
      DOTCapture.Acyclic.GeneralExpression.Erasure.eraseValue value := by
  unfold Erasure.eraseValue
    DOTCapture.Acyclic.GeneralExpression.Erasure.eraseValue
  rw [eraseValueWith_embed]
  rw [identity_eq_m10]

/-- This is the cumulative-language conservativity theorem: the M10
computational program is preserved literally by independent erasure. -/
@[simp]
theorem eraseTerm_embed {scope : Nat} (term : M10.Term scope) :
    Erasure.eraseTerm (embedTerm term) =
      DOTCapture.Acyclic.GeneralExpression.Erasure.eraseTerm term := by
  unfold Erasure.eraseTerm
    DOTCapture.Acyclic.GeneralExpression.Erasure.eraseTerm
  rw [eraseTermWith_embed]
  rw [identity_eq_m10]

end DOTCapture.Intersections.GeneralExpression.Embedding
