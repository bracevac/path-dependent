import Coercions.DOT.Captures.Intersections.GeneralExpression.Embedding

/-!
# General-expression syntax and erasure examples
-/

namespace DOTCapture.Intersections.GeneralExpression.Examples

open DOTCapture.Intersections
open DOTCapture.Intersections.GeneralExpression

namespace Runtime

export ManySortedFC.Runtime (Tm)

end Runtime

def typeLabel : Source.Label := 10
def captureLabel : Source.Label := 11

/-- A two-sort interface whose one representation refers to both allocated
local members. -/
def objectType : Source.ObjectType 0 :=
  .mk
    (.inter
      (.typeMember typeLabel .bot .top)
      (.captureMember captureLabel .empty .empty))
    (.capturing
      (.ref (.localCaptureMember captureLabel))
      (.ref (.localTypeMember typeLabel)))
    .empty

/-- A generalized positive object still stores one runtime payload. -/
def objectValue : Value 0 :=
  .object objectType
    (.lam .one .one (.ret (.var .here)))

/-- A negative consumer binds that one payload as a stable path. -/
def objectConsumer : Value 0 :=
  .objectConsumer objectType .top
    (.select (.var .here) .payload)

/-- Native object application states the expected source interface. -/
def objectApplication : Term 0 :=
  .objectApp objectType (.ret objectConsumer) (.ret objectValue)

/-- An arbitrary producer becomes a stable root only at an explicit object
let. -/
def explicitObjectLet : Term 0 :=
  .objectLet objectType .top (.ret objectValue)
    (.select (.var .here) .payload)

example : Erasure.eraseValue objectValue = .lam (.var 0) := rfl

example : Erasure.eraseValue objectConsumer = .lam (.var 0) := rfl

example : Erasure.eraseTerm objectApplication =
    .app (.lam (.var 0)) (.lam (.var 0)) := rfl

example : Erasure.eraseTerm explicitObjectLet =
    .let' (.lam (.var 0)) (.var 0) := rfl

example : ObjectArgument.classify (.ret objectValue) =
    .canonicalLiteral := rfl

example : ObjectArgument.classify
    (.objectApp objectType (.ret objectConsumer) (.ret objectValue)) =
    .requiresExplicitOpen := rfl

/-! ## M10 remains an explicitly embedded sublanguage -/

def m10Signature : DOTCapture.Acyclic.ObjectSig 0 :=
  .bounds .bot .top .empty .empty

def m10Object : DOTCapture.Acyclic.GeneralExpression.Value 0 :=
  .object m10Signature .one .empty .unit

def m10Program : DOTCapture.Acyclic.GeneralExpression.Term 0 :=
  .let' .one (.ret m10Object) (.select (.var .here) .v)

example : Erasure.eraseTerm (Embedding.embedTerm m10Program) =
    DOTCapture.Acyclic.GeneralExpression.Erasure.eraseTerm m10Program :=
  Embedding.eraseTerm_embed m10Program

example : Erasure.eraseTerm (Embedding.embedTerm m10Program) =
    .let' .unit (.var 0) := rfl

end DOTCapture.Intersections.GeneralExpression.Examples
