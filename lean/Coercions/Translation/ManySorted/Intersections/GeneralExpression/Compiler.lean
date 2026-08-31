import Coercions.DOT.Captures.Intersections.GeneralExpression.Erasure
import Coercions.Translation.ManySorted.Intersections.ObjectPreparation
import Coercions.Translation.ManySorted.Intersections.Projection
import Coercions.ManySortedFC.TheoryMapComposition
import Coercions.ManySortedFC.TheoryMapCheckerCompleteness

/-!
# Target artifacts for M11 general expressions

This file is the proof-carrying target boundary of the cumulative M11
compiler.  It deliberately does not manufacture source typing derivations:
the source typing layer supplies those derivations to the recursive compiler.
The structures here record the independently checkable FC artifacts that the
recursive cases must construct.

Positive objects use one existential package and one runtime payload.
Negative consumers abstract over the complete normalized theory.  Direct
negative arguments are restricted along a genuinely cross-shape `TheoryMap`;
their runtime payload remains value-only.  An arbitrary object computation is
handled only by `CompiledOpen`, which erases to exactly one source `let`.
-/

namespace DOTCaptureToManySortedFC.Intersections.GeneralExpression.Compiler

namespace Source

abbrev Scope := DOTCapture.Intersections.Source.Scope
abbrev Ctx := DOTCapture.Intersections.Source.Ctx
abbrev Capture := DOTCapture.Intersections.Source.Capture
abbrev Ty := DOTCapture.Intersections.Source.Ty
abbrev ObjectType := DOTCapture.Intersections.Source.ObjectType
abbrev Value := DOTCapture.Intersections.GeneralExpression.Value
abbrev Term := DOTCapture.Intersections.GeneralExpression.Term

end Source

namespace Target

open ManySortedFC

abbrev Sig := ManySortedFC.Sig
abbrev Ctx := ManySortedFC.Ctx
abbrev Capture := ManySortedFC.Capture
abbrev Ty := ManySortedFC.Ty
abbrev Tm := ManySortedFC.Tm

namespace Tm

export ManySortedFC.Tm (HasType IsValue check synth synth_complete adapt)

end Tm

end Target

namespace SourceErasure

export DOTCapture.Intersections.GeneralExpression.Erasure
  (Renaming eraseValueWith eraseTermWith)

end SourceErasure

namespace Positive

export DOTCaptureToManySortedFC.Intersections.ObjectInterface
  (Literal OpenBody existentialShape objectType)

end Positive

namespace Negative

export DOTCaptureToManySortedFC.Acyclic.NegativeObjectInterface
  (Argument abstract abstract_hasType abstract_isValue applyArgument
    apply_hasType bodyType consumerType erase_abstract erase_apply)

end Negative

open ManySortedFC
open DOTCaptureToManySortedFC.Intersections

/-! ## Compiler context and independent source erasure -/

/-- The static member layout and independently checked target context carried
by the recursive compiler.  The source context is an index, not reconstructed
from target annotations. -/
structure Ready {sourceScope : Source.Scope}
    (source : Source.Ctx sourceScope) (targetScope : Target.Sig) where
  layout : StableLayout.Layout sourceScope targetScope
  target : Target.Ctx targetScope

namespace Ready

/-- Source variables projected through the stable layout to runtime indices.
This is independent of target compilation. -/
def runtimeRenaming {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope) :
    SourceErasure.Renaming sourceScope targetScope.termCount :=
  fun name => BVar.toTermIndex (ready.layout.termVar name)

def eraseValue {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope) (value : Source.Value sourceScope) :
    Runtime.Tm targetScope.termCount :=
  SourceErasure.eraseValueWith ready.runtimeRenaming value

def eraseTerm {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope) (term : Source.Term sourceScope) :
    Runtime.Tm targetScope.termCount :=
  SourceErasure.eraseTermWith ready.runtimeRenaming term

/-- Ordinary binders extend the source and target runtime projections in
lockstep. -/
def extendPlain {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope) (sourceType : Source.Ty sourceScope)
    (targetType : Target.Ty targetScope) :
    Ready (source.extendTerm sourceType) (targetScope ▹ .term) where
  layout := ready.layout.extendPlain
  target := ready.target.extendTerm targetType

@[simp]
theorem runtimeRenaming_extendPlain {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope) (sourceType : Source.Ty sourceScope)
    (targetType : Target.Ty targetScope) :
    (ready.extendPlain sourceType targetType).runtimeRenaming =
      ready.runtimeRenaming.lift := by
  funext name
  cases name <;> rfl

end Ready

/-! ## Object preparation and the stable opening boundary -/

/-- A source object type normalized and encoded in this exact compiler
layout. -/
structure Prepared {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope) (sourceObject : Source.ObjectType sourceScope)
    where
  object : ObjectPreparation.PreparedObject targetScope
  prepared : ObjectPreparation.prepareObject ready.layout sourceObject =
    .ok object

namespace Prepared

/-- Opening a prepared object installs its complete static theory and exactly
one runtime payload binder. -/
def openedReady {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {sourceObject : Source.ObjectType sourceScope}
    (prepared : Prepared ready sourceObject) :
  Ready
      (source.extendTerm
        (DOTCapture.Intersections.GeneralExpression.ObjectType.formedType
          sourceObject))
      (PayloadScope targetScope prepared.object.encoding.symbols
        prepared.object.encoding.relations) where
  layout := ready.layout.extendObject prepared.object.encoding
  target := (ready.target.extendTheory prepared.object.encoding.theory).extendTerm
    prepared.object.representation

end Prepared

/-! ## Positive object values -/

/-- A generalized source literal compiled to the generic one-payload positive
object interface. -/
structure CompiledLiteral {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope) (sourceObject : Source.ObjectType sourceScope)
    (payload : Source.Value sourceScope) where
  prepared : Prepared ready sourceObject
  literal : Positive.Literal ready.target prepared.object.encoding.theory
    prepared.object.representation prepared.object.outerCapture
  payloadErasure : literal.payload.erase = ready.eraseValue payload

namespace CompiledLiteral

def term {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {sourceObject : Source.ObjectType sourceScope}
    {payload : Source.Value sourceScope}
    (compiled : CompiledLiteral ready sourceObject payload) : Target.Tm targetScope :=
  compiled.literal.term

def targetType {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {sourceObject : Source.ObjectType sourceScope}
    {payload : Source.Value sourceScope}
    (compiled : CompiledLiteral ready sourceObject payload) : Target.Ty targetScope :=
  compiled.prepared.object.targetType

theorem isValue {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {sourceObject : Source.ObjectType sourceScope}
    {payload : Source.Value sourceScope}
    (compiled : CompiledLiteral ready sourceObject payload) :
    Target.Tm.IsValue compiled.term :=
  compiled.literal.isValue

def typing {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {sourceObject : Source.ObjectType sourceScope}
    {payload : Source.Value sourceScope}
    (compiled : CompiledLiteral ready sourceObject payload) :
    Target.Tm.HasType ready.target compiled.term .empty compiled.targetType :=
  compiled.literal.typing

/-- The existential package, complete static model, and all annotations erase;
only the source literal's one payload remains. -/
@[simp]
theorem exactErasure {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {sourceObject : Source.ObjectType sourceScope}
    {payload : Source.Value sourceScope}
    (compiled : CompiledLiteral ready sourceObject payload) :
    compiled.term.erase =
      ready.eraseValue (.object sourceObject payload) := by
  change compiled.literal.term.erase = _
  rw [DOTCaptureToManySortedFC.Intersections.ObjectInterface.Literal.erase_term,
    compiled.payloadErasure]
  rfl

theorem checkerAccepts {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {sourceObject : Source.ObjectType sourceScope}
    {payload : Source.Value sourceScope}
    (compiled : CompiledLiteral ready sourceObject payload) :
    (Target.Tm.check ready.target compiled.term).isSome = true :=
  compiled.literal.checker_accepts

end CompiledLiteral

/-! ## Cross-shape negative argument views -/

/-- An already available model and value payload.  Canonical literals
immediately provide this data.  A stable root provides it only after the
recursive compiler reconstructs the model from the names and evidence already
opened in its target context.  An arbitrary computation provides neither. -/
structure AvailableObject {scope : Target.Sig} (context : Target.Ctx scope)
    (object : ObjectPreparation.PreparedObject scope) where
  model : Theory.Model context object.encoding.theory
  payload : Target.Tm scope
  payloadValue : Target.Tm.IsValue payload
  payloadTyping : Target.Tm.HasType context payload .empty
    (object.representation.instantiateStatic model.symbols)

namespace CompiledLiteral

def available {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {sourceObject : Source.ObjectType sourceScope}
    {payload : Source.Value sourceScope}
    (compiled : CompiledLiteral ready sourceObject payload) :
    AvailableObject ready.target compiled.prepared.object where
  model := compiled.literal.model
  payload := compiled.literal.payload
  payloadValue := compiled.literal.payloadValue
  payloadTyping := compiled.literal.payloadTyping

end CompiledLiteral

/-- A consumer view of an available object.  The endpoint types enforce the
required direction: the actual object's normalized theory interprets the
independently normalized expected theory. -/
structure ObjectView {scope : Target.Sig} (context : Target.Ctx scope)
    (actual expected : ObjectPreparation.PreparedObject scope) where
  mapping : TheoryMap actual.encoding.theory expected.encoding.theory
  typing : TheoryMap.HasType context mapping

namespace ObjectView

theorem checkerAccepts {scope : Target.Sig} {context : Target.Ctx scope}
    {actual expected : ObjectPreparation.PreparedObject scope}
    (view : ObjectView context actual expected) :
    (TheoryMap.check context view.mapping).isSome = true :=
  TheoryMap.check_isSome_iff.mpr ⟨view.typing⟩

/-- Executable restriction of an actual model to the independently normalized
expected theory. -/
def restrict? {scope : Target.Sig} {context : Target.Ctx scope}
    {actual expected : ObjectPreparation.PreparedObject scope}
    (view : ObjectView context actual expected)
    (model : Theory.Model context actual.encoding.theory) :
    Option (Theory.CheckedModel context expected.encoding.theory) :=
  TheoryMap.checkModel view.mapping model

end ObjectView

/-- A particular model restriction accepted by the standalone model checker. -/
structure CheckedRestriction {scope : Target.Sig}
    {context : Target.Ctx scope}
    {actual expected : ObjectPreparation.PreparedObject scope}
    (view : ObjectView context actual expected)
    (available : AvailableObject context actual) where
  checked : Theory.CheckedModel context expected.encoding.theory
  accepted : view.restrict? available.model = some checked

/-- Value-only transport from the actual representation to the expected
representation.  Exact erasure is recorded explicitly: adapters that would
eta-expand or insert an administrative runtime binding cannot silently weaken
the compiler theorem. -/
structure PayloadTransport {scope : Target.Sig}
    {context : Target.Ctx scope}
    {actual expected : ObjectPreparation.PreparedObject scope}
    {view : ObjectView context actual expected}
    {available : AvailableObject context actual}
    (restriction : CheckedRestriction view available) where
  adapter : Adapter scope
  adapterTyping : Adapter.HasType context adapter
    (actual.representation.instantiateStatic available.model.symbols)
    (expected.representation.instantiateStatic restriction.checked.symbols)
  exactErasure : (Target.Tm.adapt available.payload adapter).erase =
    available.payload.erase

namespace PayloadTransport

def term {scope : Target.Sig} {context : Target.Ctx scope}
    {actual expected : ObjectPreparation.PreparedObject scope}
    {view : ObjectView context actual expected}
    {available : AvailableObject context actual}
    {restriction : CheckedRestriction view available}
    (transport : PayloadTransport restriction) : Target.Tm scope :=
  .adapt available.payload transport.adapter

theorem isValue {scope : Target.Sig} {context : Target.Ctx scope}
    {actual expected : ObjectPreparation.PreparedObject scope}
    {view : ObjectView context actual expected}
    {available : AvailableObject context actual}
    {restriction : CheckedRestriction view available}
    (transport : PayloadTransport restriction) :
    Target.Tm.IsValue transport.term :=
  .adapt available.payloadValue

def typing {scope : Target.Sig} {context : Target.Ctx scope}
    {actual expected : ObjectPreparation.PreparedObject scope}
    {view : ObjectView context actual expected}
    {available : AvailableObject context actual}
    {restriction : CheckedRestriction view available}
    (transport : PayloadTransport restriction) :
    Target.Tm.HasType context transport.term .empty
      (expected.representation.instantiateStatic
        restriction.checked.symbols) :=
  .adapt available.payloadValue available.payloadTyping
    transport.adapterTyping

end PayloadTransport

/-- Direct negative elaboration of a canonical object or stable path.  The
source term is retained solely for the independent exact-erasure equation. -/
structure CompiledObjectArgument {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    (actual expected : ObjectPreparation.PreparedObject targetScope)
    (sourceTerm : Source.Term sourceScope) where
  available : AvailableObject ready.target actual
  view : ObjectView ready.target actual expected
  restriction : CheckedRestriction view available
  transport : PayloadTransport restriction
  sourceErasure : available.payload.erase = ready.eraseTerm sourceTerm

namespace CompiledObjectArgument

def target {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope}
    {actual expected : ObjectPreparation.PreparedObject targetScope}
    {sourceTerm : Source.Term sourceScope}
    (compiled : CompiledObjectArgument ready actual expected sourceTerm) :
    Negative.Argument ready.target expected.encoding.theory
      expected.representation where
  symbols := compiled.restriction.checked.symbols
  evidence := compiled.restriction.checked.evidence
  satisfies := compiled.restriction.checked.satisfies
  payload := compiled.transport.term
  payloadValue := compiled.transport.isValue
  payloadTyping := compiled.transport.typing

@[simp]
theorem exactErasure {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope}
    {actual expected : ObjectPreparation.PreparedObject targetScope}
    {sourceTerm : Source.Term sourceScope}
    (compiled : CompiledObjectArgument ready actual expected sourceTerm) :
    compiled.target.payload.erase = ready.eraseTerm sourceTerm := by
  calc
    compiled.target.payload.erase = compiled.available.payload.erase := by
      simpa [CompiledObjectArgument.target, PayloadTransport.term] using
        compiled.transport.exactErasure
    _ = ready.eraseTerm sourceTerm := compiled.sourceErasure

/-- Canonical positive literals expose their model and payload directly for
negative use; no package/open redex is constructed. -/
def ofLiteral {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {sourceObject : Source.ObjectType sourceScope}
    {payload : Source.Value sourceScope}
    (literal : CompiledLiteral ready sourceObject payload)
    (expected : ObjectPreparation.PreparedObject targetScope)
    (view : ObjectView ready.target literal.prepared.object expected)
    (restriction : CheckedRestriction view literal.available)
    (transport : PayloadTransport restriction) :
    CompiledObjectArgument ready literal.prepared.object expected
      (.ret (.object sourceObject payload)) where
  available := literal.available
  view := view
  restriction := restriction
  transport := transport
  sourceErasure := by
    simpa [Ready.eraseTerm, Ready.eraseValue] using literal.payloadErasure

end CompiledObjectArgument

/-! ## Full-theory negative consumers and direct application -/

/-- Target artifact for one negative object consumer.  Static abstraction
ranges over the complete normalized theory, and its body binds exactly the
single runtime representation. -/
structure CompiledConsumer {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope) (parameter : Source.ObjectType sourceScope)
    (sourceResult : Source.Ty sourceScope)
    (sourceBody : Source.Term (sourceScope + 1)) where
  prepared : Prepared ready parameter
  result : Target.Ty
    (StaticScope targetScope prepared.object.encoding.symbols
      prepared.object.encoding.relations)
  outerClosure : Target.Capture targetScope
  innerClosure : Target.Capture
    (StaticScope targetScope prepared.object.encoding.symbols
      prepared.object.encoding.relations)
  body : Target.Tm
    (PayloadScope targetScope prepared.object.encoding.symbols
      prepared.object.encoding.relations)
  bodyUse : Target.Capture
    (PayloadScope targetScope prepared.object.encoding.symbols
      prepared.object.encoding.relations)
  bodyCaptures : Evidence (.inclusion .capture)
    (PayloadScope targetScope prepared.object.encoding.symbols
      prepared.object.encoding.relations)
  staticCaptures : Evidence (.inclusion .capture)
    (StaticScope targetScope prepared.object.encoding.symbols
      prepared.object.encoding.relations)
  bodyTyping : Target.Tm.HasType prepared.openedReady.target body bodyUse
    result.weaken
  bodyCaptureTyping : Evidence.Proves prepared.openedReady.target bodyCaptures
    (.inclusion (.capture bodyUse)
      (.capture (.union innerClosure.weaken (.singleton .here))))
  staticCaptureTyping : Evidence.Proves
    (ready.target.extendTheory prepared.object.encoding.theory) staticCaptures
    (.inclusion (.capture innerClosure)
      (.capture (outerClosure.rename
        (Rename.weakenStatic prepared.object.encoding.symbols
          prepared.object.encoding.relations))))
  bodyErasure :
    body.eraseWith
      ((ManySortedFC.Erasure.Renaming.identity targetScope).liftPayload
        prepared.object.encoding.symbols prepared.object.encoding.relations) =
      SourceErasure.eraseTermWith ready.runtimeRenaming.lift sourceBody

namespace CompiledConsumer

def targetType {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {parameter : Source.ObjectType sourceScope}
    {sourceResult : Source.Ty sourceScope}
    {sourceBody : Source.Term (sourceScope + 1)}
    (compiled : CompiledConsumer ready parameter sourceResult sourceBody) :
    Target.Ty targetScope :=
  Negative.consumerType compiled.prepared.object.encoding.theory
    compiled.prepared.object.representation compiled.result
    compiled.outerClosure compiled.innerClosure

def term {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {parameter : Source.ObjectType sourceScope}
    {sourceResult : Source.Ty sourceScope}
    {sourceBody : Source.Term (sourceScope + 1)}
    (compiled : CompiledConsumer ready parameter sourceResult sourceBody) :
    Target.Tm targetScope :=
  Negative.abstract compiled.prepared.object.encoding.theory
    compiled.prepared.object.representation compiled.result
    compiled.outerClosure compiled.innerClosure compiled.body
    compiled.bodyCaptures compiled.staticCaptures

theorem isValue {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {parameter : Source.ObjectType sourceScope}
    {sourceResult : Source.Ty sourceScope}
    {sourceBody : Source.Term (sourceScope + 1)}
    (compiled : CompiledConsumer ready parameter sourceResult sourceBody) :
    Target.Tm.IsValue compiled.term :=
  Negative.abstract_isValue _ _ _ _ _ _ _ _

def typing {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {parameter : Source.ObjectType sourceScope}
    {sourceResult : Source.Ty sourceScope}
    {sourceBody : Source.Term (sourceScope + 1)}
    (compiled : CompiledConsumer ready parameter sourceResult sourceBody) :
    Target.Tm.HasType ready.target compiled.term .empty compiled.targetType :=
  Negative.abstract_hasType compiled.bodyTyping compiled.bodyCaptureTyping
    compiled.staticCaptureTyping

/-- Static abstraction erases literally to the source object lambda. -/
@[simp]
theorem exactErasure {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {parameter : Source.ObjectType sourceScope}
    {sourceResult : Source.Ty sourceScope}
    {sourceBody : Source.Term (sourceScope + 1)}
    (compiled : CompiledConsumer ready parameter sourceResult sourceBody) :
    compiled.term.erase =
      ready.eraseValue (.objectConsumer parameter sourceResult sourceBody) := by
  change
    (Negative.abstract compiled.prepared.object.encoding.theory
      compiled.prepared.object.representation compiled.result
      compiled.outerClosure compiled.innerClosure compiled.body
      compiled.bodyCaptures compiled.staticCaptures).erase = _
  rw [Negative.erase_abstract]
  change Runtime.Tm.lam _ = Runtime.Tm.lam _
  exact congrArg Runtime.Tm.lam compiled.bodyErasure

theorem checkerAccepts {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {parameter : Source.ObjectType sourceScope}
    {sourceResult : Source.Ty sourceScope}
    {sourceBody : Source.Term (sourceScope + 1)}
    (compiled : CompiledConsumer ready parameter sourceResult sourceBody) :
    (Target.Tm.check ready.target compiled.term).isSome = true := by
  have complete := Target.Tm.synth_complete compiled.typing
  unfold Target.Tm.synth at complete
  cases checked : Target.Tm.check ready.target compiled.term with
  | none => simp [checked] at complete
  | some _ => rfl

end CompiledConsumer

/-- A possibly computed function already compiled at the expected negative
consumer type. -/
structure CompiledObjectFunction {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    (expected : ObjectPreparation.PreparedObject targetScope)
    (sourceTerm : Source.Term sourceScope) where
  targetUse : Target.Capture targetScope
  result : Target.Ty
    (StaticScope targetScope expected.encoding.symbols
      expected.encoding.relations)
  outerClosure : Target.Capture targetScope
  innerClosure : Target.Capture
    (StaticScope targetScope expected.encoding.symbols
      expected.encoding.relations)
  term : Target.Tm targetScope
  typing : Target.Tm.HasType ready.target term targetUse
    (Negative.consumerType expected.encoding.theory expected.representation
      result outerClosure innerClosure)
  exactErasure : term.erase = ready.eraseTerm sourceTerm

namespace CompiledObjectFunction

/-- A compiled object consumer is immediately a value-producing negative
function artifact over its complete normalized theory. -/
def ofConsumer {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {parameter : Source.ObjectType sourceScope}
    {sourceResult : Source.Ty sourceScope}
    {sourceBody : Source.Term (sourceScope + 1)}
    (consumer : CompiledConsumer ready parameter sourceResult sourceBody) :
    CompiledObjectFunction ready consumer.prepared.object
      (.ret (.objectConsumer parameter sourceResult sourceBody)) where
  targetUse := .empty
  result := consumer.result
  outerClosure := consumer.outerClosure
  innerClosure := consumer.innerClosure
  term := consumer.term
  typing := consumer.typing
  exactErasure := consumer.exactErasure

end CompiledObjectFunction

/-- Direct object application: static model application followed by ordinary
runtime payload application. -/
structure CompiledObjectApplication {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    (expected : ObjectPreparation.PreparedObject targetScope)
    (sourceParameter : Source.ObjectType sourceScope)
    (function argument : Source.Term sourceScope) where
  actual : ObjectPreparation.PreparedObject targetScope
  functionCompiled : CompiledObjectFunction ready expected function
  argumentCompiled : CompiledObjectArgument ready
    actual expected argument

namespace CompiledObjectApplication

def term {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope}
    {expected : ObjectPreparation.PreparedObject targetScope}
    {sourceParameter : Source.ObjectType sourceScope}
    {function argument : Source.Term sourceScope}
    (compiled : CompiledObjectApplication ready expected sourceParameter
      function argument) :
    Target.Tm targetScope :=
  Negative.applyArgument expected.encoding.theory
    compiled.functionCompiled.term compiled.argumentCompiled.target

def typing {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope}
    {expected : ObjectPreparation.PreparedObject targetScope}
    {sourceParameter : Source.ObjectType sourceScope}
    {function argument : Source.Term sourceScope}
    (compiled : CompiledObjectApplication ready expected sourceParameter
      function argument) :
    Target.Tm.HasType ready.target compiled.term
      ((compiled.functionCompiled.targetUse.sequence
        compiled.functionCompiled.outerClosure).sequence
        (.union
          ((Negative.bodyType expected.representation
            compiled.functionCompiled.result
            compiled.functionCompiled.innerClosure).instantiateStatic
              compiled.argumentCompiled.target.symbols).outerCapture
          (expected.representation.instantiateStatic
            compiled.argumentCompiled.target.symbols).outerCapture))
      (compiled.functionCompiled.result.instantiateStatic
        compiled.argumentCompiled.target.symbols) :=
  Negative.apply_hasType compiled.functionCompiled.typing
    compiled.argumentCompiled.target

@[simp]
theorem exactErasure {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope}
    {expected : ObjectPreparation.PreparedObject targetScope}
    {sourceParameter : Source.ObjectType sourceScope}
    {function argument : Source.Term sourceScope}
    (compiled : CompiledObjectApplication ready expected sourceParameter
      function argument) :
    compiled.term.erase =
      ready.eraseTerm (.objectApp sourceParameter function argument) := by
  change
    (Negative.applyArgument expected.encoding.theory
      compiled.functionCompiled.term compiled.argumentCompiled.target).erase = _
  rw [Negative.erase_apply, compiled.functionCompiled.exactErasure,
    compiled.argumentCompiled.exactErasure]
  rfl

theorem checkerAccepts {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope}
    {expected : ObjectPreparation.PreparedObject targetScope}
    {sourceParameter : Source.ObjectType sourceScope}
    {function argument : Source.Term sourceScope}
    (compiled : CompiledObjectApplication ready expected sourceParameter
      function argument) :
    (Target.Tm.check ready.target compiled.term).isSome = true := by
  have complete := Target.Tm.synth_complete compiled.typing
  unfold Target.Tm.synth at complete
  cases checked : Target.Tm.check ready.target compiled.term with
  | none => simp [checked] at complete
  | some _ => rfl

end CompiledObjectApplication

/-! ## Explicit opening of arbitrary object computations -/

/-- The only compiler artifact that turns an arbitrary object-producing
computation into a stable root.  It uses the generic one-payload target open
and records the exact source `objectLet` erasure. -/
structure CompiledOpen {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope) (sourceObject : Source.ObjectType sourceScope)
    (sourceResult : Source.Ty sourceScope) (rhs : Source.Term sourceScope)
    (body : Source.Term (sourceScope + 1)) where
  prepared : Prepared ready sourceObject
  result : Target.Ty targetScope
  resultTranslated : ObjectPreparation.translateType ready.layout sourceResult =
    .ok result
  packageUse : Target.Capture targetScope
  packageType : Target.Ty targetScope
  package : Target.Tm targetScope
  packageTyping : Target.Tm.HasType ready.target package packageUse packageType
  packageShape : packageType.stripCapture =
    Positive.existentialShape prepared.object.encoding.theory
      prepared.object.representation
  bodyOuterUse : Target.Capture targetScope
  opened : Positive.OpenBody ready.target prepared.object.encoding.theory
    prepared.object.representation result bodyOuterUse
  packageErasure : package.erase = ready.eraseTerm rhs
  bodyErasure : opened.body.eraseWith
      ((ManySortedFC.Erasure.Renaming.identity targetScope).liftPayload
        prepared.object.encoding.symbols prepared.object.encoding.relations) =
    SourceErasure.eraseTermWith ready.runtimeRenaming.lift body

namespace CompiledOpen

def term {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {sourceObject : Source.ObjectType sourceScope}
    {sourceResult : Source.Ty sourceScope} {rhs : Source.Term sourceScope}
    {body : Source.Term (sourceScope + 1)}
    (compiled : CompiledOpen ready sourceObject sourceResult rhs body) :
    Target.Tm targetScope :=
  compiled.opened.term compiled.packageTyping compiled.packageShape

def typing {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {sourceObject : Source.ObjectType sourceScope}
    {sourceResult : Source.Ty sourceScope} {rhs : Source.Term sourceScope}
    {body : Source.Term (sourceScope + 1)}
    (compiled : CompiledOpen ready sourceObject sourceResult rhs body) :
    Target.Tm.HasType ready.target compiled.term
      (compiled.packageUse.sequence
        (.union compiled.packageType.outerCapture compiled.bodyOuterUse))
      compiled.result :=
  compiled.opened.typing compiled.packageTyping compiled.packageShape

@[simp]
theorem exactErasure {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {sourceObject : Source.ObjectType sourceScope}
    {sourceResult : Source.Ty sourceScope} {rhs : Source.Term sourceScope}
    {body : Source.Term (sourceScope + 1)}
    (compiled : CompiledOpen ready sourceObject sourceResult rhs body) :
    compiled.term.erase =
      ready.eraseTerm (.objectLet sourceObject sourceResult rhs body) := by
  change
    (compiled.opened.term compiled.packageTyping
      compiled.packageShape).erase = _
  rw [DOTCaptureToManySortedFC.Intersections.ObjectInterface.OpenBody.erase_term]
  change Runtime.Tm.let' compiled.package.erase _ =
    Runtime.Tm.let' (ready.eraseTerm rhs)
      (SourceErasure.eraseTermWith ready.runtimeRenaming.lift body)
  congr
  · exact compiled.packageErasure
  · simpa using compiled.bodyErasure

theorem checkerAccepts {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {sourceObject : Source.ObjectType sourceScope}
    {sourceResult : Source.Ty sourceScope} {rhs : Source.Term sourceScope}
    {body : Source.Term (sourceScope + 1)}
    (compiled : CompiledOpen ready sourceObject sourceResult rhs body) :
    (Target.Tm.check ready.target compiled.term).isSome = true := by
  have complete := Target.Tm.synth_complete compiled.typing
  unfold Target.Tm.synth at complete
  cases checked : Target.Tm.check ready.target compiled.term with
  | none => simp [checked] at complete
  | some _ => rfl

end CompiledOpen

end DOTCaptureToManySortedFC.Intersections.GeneralExpression.Compiler
