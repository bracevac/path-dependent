import Coercions.ManySortedFC.TermCheckerCompleteness
import Coercions.ManySortedFC.Erasure

/-!
# Negative object interfaces

An object interface is represented positively by an existential package, but
its negative use does not need to construct and immediately open that package.
This module records the target-side negative form for an arbitrary names-first
theory and representation type:

```
  forall model, representation model -> result model
```

The construction is independent of the fixed two-member acyclic encoding.
Later signature constructions can reuse it by supplying a different theory and
representation type.  Static abstraction remains value-restricted; only static
application may evaluate its function scrutinee.
-/

namespace DOTCaptureToManySortedFC.Acyclic.NegativeObjectInterface

open ManySortedFC

/-- The runtime function exposed after a model has been supplied.  Both its
closure and its result may mention the abstract names introduced by `theory`.
-/
def bodyType {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (representation result :
      Ty (StaticScope scope symbols relations))
    (closure : Capture (StaticScope scope symbols relations)) :
    Ty (StaticScope scope symbols relations) :=
  .capturing closure (.arr representation result)

/-- The actual type produced by an object-consumer static abstraction.  The
outer capture belongs to the ambient program; the inner capture is the closure
of the runtime function after the model telescope has been introduced.
-/
def consumerType {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (theory : Theory scope symbols relations)
    (representation result : Ty (StaticScope scope symbols relations))
    (outerClosure : Capture scope)
    (innerClosure : Capture (StaticScope scope symbols relations)) : Ty scope :=
  .capturing outerClosure
    (.forallT theory (bodyType representation result innerClosure))

/-- The common nondependent-result specialization. -/
def ambientResultType {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (theory : Theory scope symbols relations)
    (representation : Ty (StaticScope scope symbols relations))
    (result : Ty scope) (closure : Capture scope) : Ty scope :=
  consumerType theory representation
    (result.rename (Rename.weakenStatic symbols relations)) closure
    (closure.rename (Rename.weakenStatic symbols relations))

/-- Build the target object consumer.  The ordinary lambda is already a
value, so erasing the surrounding static abstraction cannot expose an early
computation.
-/
def abstract {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (theory : Theory scope symbols relations)
    (representation result : Ty (StaticScope scope symbols relations))
    (outerClosure : Capture scope)
    (innerClosure : Capture (StaticScope scope symbols relations))
    (body : Tm (PayloadScope scope symbols relations))
    (bodyCaptures : Evidence (.inclusion .capture)
      (PayloadScope scope symbols relations))
    (staticCaptures : Evidence (.inclusion .capture)
      (StaticScope scope symbols relations)) : Tm scope :=
  .slam theory outerClosure
    (.lam representation result innerClosure body bodyCaptures)
    staticCaptures

/-- A model and its already available runtime representation, ready for
negative use.  This is deliberately proof-relevant and indexed by the expected
interface.  It cannot contain an arbitrary computation: the payload must be an
annotated value with empty immediate use.
-/
structure Argument {scope : Sig} (context : Ctx scope)
    {symbols : List StaticSort} {relations : List Relation}
    (theory : Theory scope symbols relations)
    (representation : Ty (StaticScope scope symbols relations)) where
  symbols : SymbolArgs scope symbols
  evidence : EvidenceArgs scope relations
  satisfies : Theory.SatisfiedBy context symbols theory evidence
  payload : Tm scope
  payloadValue : Tm.IsValue payload
  payloadTyping : Tm.HasType context payload .empty
    (representation.instantiateStatic symbols)

/-- Supply a model statically, then pass its representation directly to the
runtime function.  No existential package or opening node is introduced.
-/
def applyArgument {scope : Sig} {context : Ctx scope}
    {symbols : List StaticSort} {relations : List Relation}
    (theory : Theory scope symbols relations)
    {representation : Ty (StaticScope scope symbols relations)}
    (function : Tm scope) (argument : Argument context theory representation) :
    Tm scope :=
  .app (.sapp theory function argument.symbols argument.evidence)
    argument.payload

/-- Declarative typing for the generic object-consumer abstraction. -/
def abstract_hasType {scope : Sig} {context : Ctx scope}
    {symbols : List StaticSort} {relations : List Relation}
    {theory : Theory scope symbols relations}
    {representation result : Ty (StaticScope scope symbols relations)}
    {outerClosure : Capture scope}
    {innerClosure : Capture (StaticScope scope symbols relations)}
    {body : Tm (PayloadScope scope symbols relations)}
    {bodyUse : Capture (PayloadScope scope symbols relations)}
    {bodyCaptures : Evidence (.inclusion .capture)
      (PayloadScope scope symbols relations)}
    {staticCaptures : Evidence (.inclusion .capture)
      (StaticScope scope symbols relations)}
    (bodyTyping : Tm.HasType
      ((context.extendTheory theory).extendTerm representation)
      body bodyUse result.weaken)
    (bodyCaptureTyping : Evidence.Proves
      ((context.extendTheory theory).extendTerm representation)
      bodyCaptures
      (.inclusion (.capture bodyUse)
        (.capture (.union innerClosure.weaken (.singleton .here)))))
    (staticCaptureTyping : Evidence.Proves (context.extendTheory theory)
      staticCaptures
      (.inclusion (.capture innerClosure)
        (.capture (outerClosure.rename
          (Rename.weakenStatic symbols relations))))) :
    Tm.HasType context
      (abstract theory representation result outerClosure innerClosure body
        bodyCaptures staticCaptures)
      .empty
      (consumerType theory representation result outerClosure innerClosure) := by
  exact .slam .lam (.lam bodyTyping bodyCaptureTyping) staticCaptureTyping

/-- The generic abstraction is an actual captured static-lambda value. -/
theorem abstract_isValue {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (theory : Theory scope symbols relations)
    (representation result : Ty (StaticScope scope symbols relations))
    (outerClosure : Capture scope)
    (innerClosure : Capture (StaticScope scope symbols relations))
    (body : Tm (PayloadScope scope symbols relations))
    (bodyCaptures : Evidence (.inclusion .capture)
      (PayloadScope scope symbols relations))
    (staticCaptures : Evidence (.inclusion .capture)
      (StaticScope scope symbols relations)) :
    Tm.IsValue (abstract theory representation result outerClosure innerClosure
      body bodyCaptures staticCaptures) :=
  .slam .lam

/-- Typing of direct negative application.  The function computation is
evaluated by `sapp`; the available representation is then passed to the
ordinary runtime function.
-/
def apply_hasType {scope : Sig} {context : Ctx scope}
    {symbols : List StaticSort} {relations : List Relation}
    {theory : Theory scope symbols relations}
    {representation result : Ty (StaticScope scope symbols relations)}
    {outerClosure : Capture scope}
    {innerClosure : Capture (StaticScope scope symbols relations)}
    {function : Tm scope} {functionUse : Capture scope}
    (functionTyping : Tm.HasType context function functionUse
      (consumerType theory representation result outerClosure innerClosure))
    (argument : Argument context theory representation) :
    Tm.HasType context (applyArgument theory function argument)
      ((functionUse.sequence outerClosure).sequence
        (.union
          ((bodyType representation result innerClosure).instantiateStatic
            argument.symbols).outerCapture
          (representation.instantiateStatic argument.symbols).outerCapture))
      (result.instantiateStatic argument.symbols) := by
  have staticTyping :=
    Tm.HasType.sapp functionTyping (by rfl) argument.satisfies
  have applicationTyping := Tm.HasType.app staticTyping (by rfl)
    argument.payloadTyping
  simpa [applyArgument, consumerType, bodyType] using applicationTyping

/-- Static abstraction and all model annotations erase; only the ordinary
runtime lambda remains.
-/
@[simp]
theorem erase_abstract {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (theory : Theory scope symbols relations)
    (representation result : Ty (StaticScope scope symbols relations))
    (outerClosure : Capture scope)
    (innerClosure : Capture (StaticScope scope symbols relations))
    (body : Tm (PayloadScope scope symbols relations))
    (bodyCaptures : Evidence (.inclusion .capture)
      (PayloadScope scope symbols relations))
    (staticCaptures : Evidence (.inclusion .capture)
      (StaticScope scope symbols relations)) :
    (abstract theory representation result outerClosure innerClosure body
      bodyCaptures staticCaptures).erase =
      .lam (body.eraseWith
        (Erasure.Renaming.liftTerm
          ((Erasure.Renaming.identity scope).liftStatic symbols relations))) :=
  rfl

/-- Direct negative application erases literally to source-shaped runtime
application.  In particular, no package/open redex is present.
-/
@[simp]
theorem erase_apply {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} {context : Ctx scope}
    (theory : Theory scope symbols relations)
    {representation : Ty (StaticScope scope symbols relations)}
    (function : Tm scope)
    (argument : Argument context theory representation) :
    (applyArgument theory function argument).erase =
      ManySortedFC.Runtime.Tm.app function.erase argument.payload.erase := rfl

end DOTCaptureToManySortedFC.Acyclic.NegativeObjectInterface
