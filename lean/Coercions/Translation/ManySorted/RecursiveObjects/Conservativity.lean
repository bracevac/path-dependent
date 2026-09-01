import Coercions.DOT.Captures.ModalIntersections.CapturedTypingEmbedding
import Coercions.Translation.ManySorted.Intersections.GeneralExpression.CompilerConservativity
import Coercions.Translation.ManySorted.ModalIntersections.Compiler

/-!
# Conservativity over the preceding cumulative compiler

The modal cumulative compiler has a wider adapter language than M11, so its
general artifact boundary records administrative equivalence.  This module
isolates the embedded M11 fragment and retains a cumulative result only after
its literal erasure has also been checked.  The resulting theorem compares
the target erasures of two actual independently accepted compiler artifacts;
it does not identify their static binders, evidence, or object contracts.

The statement is conditional on the two partial compilers succeeding, as are
the existing M10/M11 compiler-conservativity theorems.  Runtime compatibility
requires only that both compiler layouts project source term variables to the
same erased coordinates.
-/

namespace DOTCaptureToManySortedFC.RecursiveObjects.Conservativity

namespace Previous

abbrev Ctx := DOTCapture.Intersections.Source.Ctx
abbrev Value := DOTCapture.Intersections.GeneralExpression.Value
abbrev Term := DOTCapture.Intersections.GeneralExpression.Term
abbrev Ty := DOTCapture.Intersections.Source.Ty
abbrev Capture := DOTCapture.Intersections.Source.Capture
abbrev Ready {scope : Nat} (source : Ctx scope)
    (targetScope : ManySortedFC.Sig) :=
  DOTCaptureToManySortedFC.Intersections.GeneralExpression.Compiler.Ready
    source targetScope
abbrev CompiledValue {scope : Nat} {source : Ctx scope}
    {targetScope : ManySortedFC.Sig} (ready : Ready source targetScope)
    (value : Value scope) (type : Ty scope) :=
  DOTCaptureToManySortedFC.Intersections.GeneralExpression.Recursive.CompiledValue
    ready value type
abbrev CompiledTerm {scope : Nat} {source : Ctx scope}
    {targetScope : ManySortedFC.Sig} (ready : Ready source targetScope)
    (term : Term scope) (use : Capture scope) (type : Ty scope) :=
  DOTCaptureToManySortedFC.Intersections.GeneralExpression.Recursive.CompiledTerm
    ready term use type

end Previous

namespace Cumulative

abbrev Context {sourceScope : DOTCapture.ModalIntersections.Sig}
    (environment : DOTCapture.ModalIntersections.TypingEnv sourceScope)
    (targetScope : ManySortedFC.Sig) :=
  DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext.Context
    environment targetScope
abbrev CompiledValue {sourceScope : DOTCapture.ModalIntersections.Sig}
    {environment : DOTCapture.ModalIntersections.TypingEnv sourceScope}
    {targetScope : ManySortedFC.Sig}
    (core : DOTCaptureToManySortedFC.ModalIntersections.CompilerContext.Core
      environment targetScope)
    (value : DOTCapture.ModalIntersections.Value sourceScope)
    (type : DOTCapture.ModalIntersections.Ty sourceScope) :=
  DOTCaptureToManySortedFC.ModalIntersections.CompilerArtifacts.CompiledValue
    core value type
abbrev CompiledTerm {sourceScope : DOTCapture.ModalIntersections.Sig}
    {environment : DOTCapture.ModalIntersections.TypingEnv sourceScope}
    {targetScope : ManySortedFC.Sig}
    (core : DOTCaptureToManySortedFC.ModalIntersections.CompilerContext.Core
      environment targetScope)
    (term : DOTCapture.ModalIntersections.Term sourceScope)
    (use : DOTCapture.ModalIntersections.Capture sourceScope)
    (type : DOTCapture.ModalIntersections.Ty sourceScope) :=
  DOTCaptureToManySortedFC.ModalIntersections.CompilerArtifacts.CompiledTerm
    core term use type

end Cumulative

namespace Embed

abbrev environment {scope : Nat} (source : Previous.Ctx scope) :=
  DOTCapture.ModalIntersections.Embedding.CapturedIntersections.typingEnvironment
    source
abbrev value {scope : Nat} (source : Previous.Value scope) :=
  DOTCapture.ModalIntersections.Embedding.value source
abbrev term {scope : Nat} (source : Previous.Term scope) :=
  DOTCapture.ModalIntersections.Embedding.term source
abbrev type {scope : Nat} (source : Previous.Ty scope) :=
  DOTCapture.ModalIntersections.Embedding.type source
abbrev capture {scope : Nat} (source : Previous.Capture scope) :=
  DOTCapture.ModalIntersections.Embedding.capture source
abbrev valueTyping {scope : Nat} {source : Previous.Ctx scope}
    {value : Previous.Value scope} {type : Previous.Ty scope}
    (typing : DOTCapture.Intersections.GeneralExpression.Value.HasType
      source value type) :=
  DOTCapture.ModalIntersections.Embedding.CapturedIntersections.valueTyping
    typing
abbrev termTyping {scope : Nat} {source : Previous.Ctx scope}
    {term : Previous.Term scope} {use : Previous.Capture scope}
    {type : Previous.Ty scope}
    (typing : DOTCapture.Intersections.GeneralExpression.Term.HasType
      source term use type) :=
  DOTCapture.ModalIntersections.Embedding.CapturedIntersections.termTyping
    typing

end Embed

open DOTCaptureToManySortedFC.ModalIntersections.Compiler
open DOTCaptureToManySortedFC.ModalIntersections.CompilerArtifacts
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext

/-- The two compiler layouts agree on erased source-variable coordinates.
Static names and evidence coordinates are deliberately absent from this
relation because both source erasures ignore them. -/
structure RuntimeAgreement {scope : Nat} {source : Previous.Ctx scope}
    {targetScope : ManySortedFC.Sig}
    (previous : Previous.Ready source targetScope)
    (cumulative : Cumulative.Context (Embed.environment source) targetScope) :
    Prop where
  runtimeRenamingEq : cumulative.core.runtimeRenaming =
    DOTCapture.ModalIntersections.Erasure.embeddedRenaming
      previous.runtimeRenaming

/-- Runtime agreement is exactly the premise required by the independently
defined source erasures. -/
theorem embeddedValueErasure {scope : Nat} {source : Previous.Ctx scope}
    {targetScope : ManySortedFC.Sig}
    {previous : Previous.Ready source targetScope}
    {cumulative : Cumulative.Context (Embed.environment source) targetScope}
    (agreement : RuntimeAgreement previous cumulative)
    (value : Previous.Value scope) :
    cumulative.core.eraseValue (Embed.value value) =
      previous.eraseValue value := by
  unfold Core.eraseValue
  unfold DOTCaptureToManySortedFC.Intersections.GeneralExpression.Compiler.Ready.eraseValue
  rw [agreement.runtimeRenamingEq]
  exact DOTCapture.ModalIntersections.Erasure.eraseValueWith_embedding
    previous.runtimeRenaming value

/-- Computation counterpart of `embeddedValueErasure`. -/
theorem embeddedTermErasure {scope : Nat} {source : Previous.Ctx scope}
    {targetScope : ManySortedFC.Sig}
    {previous : Previous.Ready source targetScope}
    {cumulative : Cumulative.Context (Embed.environment source) targetScope}
    (agreement : RuntimeAgreement previous cumulative)
    (term : Previous.Term scope) :
    cumulative.core.eraseTerm (Embed.term term) =
      previous.eraseTerm term := by
  unfold Core.eraseTerm
  unfold DOTCaptureToManySortedFC.Intersections.GeneralExpression.Compiler.Ready.eraseTerm
  rw [agreement.runtimeRenamingEq]
  exact DOTCapture.ModalIntersections.Erasure.eraseTermWith_embedding
    previous.runtimeRenaming term

/-! ## Literal-erasure cumulative compiler boundary -/

/-- A successful run of the actual cumulative value compiler on an embedded
M11 derivation, together with the additionally checked literal-erasure fact.
The ordinary cumulative artifact inside this structure already retains both
standalone target checker acceptances. -/
structure ExactEmbeddedValue {scope : Nat} {source : Previous.Ctx scope}
    {targetScope : ManySortedFC.Sig}
    (context : Cumulative.Context (Embed.environment source) targetScope)
    {value : Previous.Value scope} {type : Previous.Ty scope}
    (typing : DOTCapture.Intersections.GeneralExpression.Value.HasType
      source value type) where
  compiled : Cumulative.CompiledValue context.core
    (Embed.value value) (Embed.type type)
  compilerSuccess : compileValue context (Embed.valueTyping typing) =
    .ok compiled
  exactErasure : compiled.term.erase =
    context.core.eraseValue (Embed.value value)

/-- Execute the cumulative compiler and retain its result only when the
embedded M11 program also crosses the literal-erasure boundary. -/
def compileEmbeddedValue? {scope : Nat} {source : Previous.Ctx scope}
    {targetScope : ManySortedFC.Sig}
    (context : Cumulative.Context (Embed.environment source) targetScope)
    {value : Previous.Value scope} {type : Previous.Ty scope}
    (typing : DOTCapture.Intersections.GeneralExpression.Value.HasType
      source value type) : Option (ExactEmbeddedValue context typing) :=
  match compilerSuccess : compileValue context (Embed.valueTyping typing) with
  | .error _ => none
  | .ok compiled =>
      if exactErasure : compiled.term.erase =
          context.core.eraseValue (Embed.value value) then
        some { compiled, compilerSuccess, exactErasure }
      else
        none

/-- Computation analogue of `ExactEmbeddedValue`. -/
structure ExactEmbeddedTerm {scope : Nat} {source : Previous.Ctx scope}
    {targetScope : ManySortedFC.Sig}
    (context : Cumulative.Context (Embed.environment source) targetScope)
    {term : Previous.Term scope} {use : Previous.Capture scope}
    {type : Previous.Ty scope}
    (typing : DOTCapture.Intersections.GeneralExpression.Term.HasType
      source term use type) where
  compiled : Cumulative.CompiledTerm context.core
    (Embed.term term) (Embed.capture use) (Embed.type type)
  compilerSuccess : compileTerm context (Embed.termTyping typing) = .ok compiled
  exactErasure : compiled.term.erase =
    context.core.eraseTerm (Embed.term term)

/-- Execute the cumulative computation compiler and require literal erasure
for the embedded M11 fragment. -/
def compileEmbeddedTerm? {scope : Nat} {source : Previous.Ctx scope}
    {targetScope : ManySortedFC.Sig}
    (context : Cumulative.Context (Embed.environment source) targetScope)
    {term : Previous.Term scope} {use : Previous.Capture scope}
    {type : Previous.Ty scope}
    (typing : DOTCapture.Intersections.GeneralExpression.Term.HasType
      source term use type) : Option (ExactEmbeddedTerm context typing) :=
  match compilerSuccess : compileTerm context (Embed.termTyping typing) with
  | .error _ => none
  | .ok compiled =>
      if exactErasure : compiled.term.erase =
          context.core.eraseTerm (Embed.term term) then
        some { compiled, compilerSuccess, exactErasure }
      else
        none

/-! ## Artifact-level conservativity and checker acceptance -/

/-- Both independently accepted value artifacts and their literal runtime
equality. -/
structure ValueConservativity {scope : Nat} {source : Previous.Ctx scope}
    {targetScope : ManySortedFC.Sig}
    {previousReady : Previous.Ready source targetScope}
    {context : Cumulative.Context (Embed.environment source) targetScope}
    {value : Previous.Value scope} {type : Previous.Ty scope}
    {typing : DOTCapture.Intersections.GeneralExpression.Value.HasType
      source value type}
    (previous : Previous.CompiledValue previousReady value type)
    (cumulative : ExactEmbeddedValue context typing) : Prop where
  erasure : previous.term.erase = cumulative.compiled.term.erase
  previousAccepted : ManySortedFC.Tm.synth previousReady.target previous.term =
    some (.empty, previous.targetType)
  cumulativeAccepted : ManySortedFC.Tm.synth context.core.target
    cumulative.compiled.term = some (.empty, cumulative.compiled.targetType)
  cumulativeValueAccepted :
    (ManySortedFC.Tm.checkValue cumulative.compiled.term).isSome = true

/-- Every preceding M11 value artifact and successful exact cumulative
embedding have identical target erasures.  Both checker facts are retained in
the result rather than inferred from erasure. -/
theorem valueConservativity {scope : Nat} {source : Previous.Ctx scope}
    {targetScope : ManySortedFC.Sig}
    {previousReady : Previous.Ready source targetScope}
    {context : Cumulative.Context (Embed.environment source) targetScope}
    {value : Previous.Value scope} {type : Previous.Ty scope}
    {typing : DOTCapture.Intersections.GeneralExpression.Value.HasType
      source value type}
    (agreement : RuntimeAgreement previousReady context)
    (previous : Previous.CompiledValue previousReady value type)
    (cumulative : ExactEmbeddedValue context typing) :
    ValueConservativity previous cumulative where
  erasure := by
    calc
      previous.term.erase = previousReady.eraseValue value :=
        previous.exactErasure
      _ = context.core.eraseValue (Embed.value value) :=
        (embeddedValueErasure agreement value).symm
      _ = cumulative.compiled.term.erase := cumulative.exactErasure.symm
  previousAccepted := previous.checkerAccepts
  cumulativeAccepted := cumulative.compiled.checkerAccepts
  cumulativeValueAccepted := cumulative.compiled.valueCheckerAccepts

/-- Both independently accepted computation artifacts and their literal
runtime equality. -/
structure TermConservativity {scope : Nat} {source : Previous.Ctx scope}
    {targetScope : ManySortedFC.Sig}
    {previousReady : Previous.Ready source targetScope}
    {context : Cumulative.Context (Embed.environment source) targetScope}
    {term : Previous.Term scope} {use : Previous.Capture scope}
    {type : Previous.Ty scope}
    {typing : DOTCapture.Intersections.GeneralExpression.Term.HasType
      source term use type}
    (previous : Previous.CompiledTerm previousReady term use type)
    (cumulative : ExactEmbeddedTerm context typing) : Prop where
  erasure : previous.term.erase = cumulative.compiled.term.erase
  previousAccepted : ManySortedFC.Tm.synth previousReady.target previous.term =
    some (previous.targetUse, previous.targetType)
  cumulativeAccepted : ManySortedFC.Tm.synth context.core.target
    cumulative.compiled.term =
      some (cumulative.compiled.targetUse, cumulative.compiled.targetType)

/-- General M11-to-Stage-6 computation conservativity for two successful
compiler artifacts. -/
theorem termConservativity {scope : Nat} {source : Previous.Ctx scope}
    {targetScope : ManySortedFC.Sig}
    {previousReady : Previous.Ready source targetScope}
    {context : Cumulative.Context (Embed.environment source) targetScope}
    {term : Previous.Term scope} {use : Previous.Capture scope}
    {type : Previous.Ty scope}
    {typing : DOTCapture.Intersections.GeneralExpression.Term.HasType
      source term use type}
    (agreement : RuntimeAgreement previousReady context)
    (previous : Previous.CompiledTerm previousReady term use type)
    (cumulative : ExactEmbeddedTerm context typing) :
    TermConservativity previous cumulative where
  erasure := by
    calc
      previous.term.erase = previousReady.eraseTerm term := previous.exactErasure
      _ = context.core.eraseTerm (Embed.term term) :=
        (embeddedTermErasure agreement term).symm
      _ = cumulative.compiled.term.erase := cumulative.exactErasure.symm
  previousAccepted := previous.checkerAccepts
  cumulativeAccepted := cumulative.compiled.checkerAccepts

/-! ## Transitive M10 corollaries

The established M10/M11 theorems already compare a successful M10 compiler
run with any independently accepted M11 artifact for its embedding.  The next
two results compose that boundary with the checked M11-to-cumulative boundary
above.  No third compiler or syntactic artifact equality is assumed. -/

namespace M10

abbrev Ctx := DOTCapture.Acyclic.Ctx
abbrev Value := DOTCapture.Acyclic.GeneralExpression.Value
abbrev Term := DOTCapture.Acyclic.GeneralExpression.Term
abbrev Ty := DOTCapture.Acyclic.Ty
abbrev Capture := DOTCapture.Acyclic.Capture
abbrev Ready {scope : Nat} (source : Ctx scope) :=
  DOTCaptureToManySortedFC.Acyclic.RuntimeContext.Ready source
abbrev CompiledValue {scope : Nat} {source : Ctx scope}
    (ready : Ready source) (value : Value scope) (type : Ty scope) :=
  DOTCaptureToManySortedFC.Acyclic.GeneralExpression.Compiler.CompiledValue
    ready value type
abbrev CompiledTerm {scope : Nat} {source : Ctx scope}
    (ready : Ready source) (term : Term scope) (use : Capture scope)
    (type : Ty scope) :=
  DOTCaptureToManySortedFC.Acyclic.GeneralExpression.Compiler.CompiledTerm
    ready term use type

end M10

/-- M10-to-Stage-6 value conservativity follows by composing the existing
M10/M11 compiler theorem with `valueConservativity`. -/
theorem m10ValueErasureConservativity
    {scope : Nat} {source : M10.Ctx scope}
    {m10Ready : M10.Ready source}
    {value : M10.Value scope} {type : M10.Ty scope}
    {typing : DOTCapture.Acyclic.GeneralExpression.Value.HasType
      source value type}
    {m10Compiled : M10.CompiledValue m10Ready value type}
    (m10Success :
      DOTCaptureToManySortedFC.Acyclic.GeneralExpression.Compiler.compilePolarizedValue?
        m10Ready typing = some m10Compiled)
    {previousReady : Previous.Ready
      (DOTCapture.Intersections.GeneralExpression.Embedding.embedCtx source)
      (DOTCaptureToManySortedFC.Acyclic.Layout.sig source)}
    (previous : Previous.CompiledValue previousReady
      (DOTCapture.Intersections.GeneralExpression.Embedding.embedValue value)
      (DOTCapture.Intersections.Source.embedM10Ty type))
    (m10M11Agreement : previousReady.runtimeRenaming =
      DOTCaptureToManySortedFC.Acyclic.GeneralExpression.SourceErasure.compiledRenaming
        source)
    {context : Cumulative.Context
      (Embed.environment
        (DOTCapture.Intersections.GeneralExpression.Embedding.embedCtx source))
      (DOTCaptureToManySortedFC.Acyclic.Layout.sig source)}
    (cumulative : ExactEmbeddedValue context
      (DOTCapture.Intersections.GeneralExpression.Embedding.embedValueTyping
        typing))
    (m11Stage6Agreement : RuntimeAgreement previousReady context) :
    m10Compiled.term.erase = cumulative.compiled.term.erase := by
  exact
    (DOTCaptureToManySortedFC.Intersections.GeneralExpression.CompilerConservativity.m10_m11_value_erasure_coherent
      m10Success previous m10M11Agreement).trans
      (valueConservativity m11Stage6Agreement previous cumulative).erasure

/-- Computation counterpart of `m10ValueErasureConservativity`. -/
theorem m10TermErasureConservativity
    {scope : Nat} {source : M10.Ctx scope}
    {m10Ready : M10.Ready source}
    {term : M10.Term scope} {use : M10.Capture scope} {type : M10.Ty scope}
    {typing : DOTCapture.Acyclic.GeneralExpression.Term.HasType
      source term use type}
    {m10Compiled : M10.CompiledTerm m10Ready term use type}
    (m10Success :
      DOTCaptureToManySortedFC.Acyclic.GeneralExpression.Compiler.compilePolarizedTerm?
        m10Ready typing = some m10Compiled)
    {previousReady : Previous.Ready
      (DOTCapture.Intersections.GeneralExpression.Embedding.embedCtx source)
      (DOTCaptureToManySortedFC.Acyclic.Layout.sig source)}
    (previous : Previous.CompiledTerm previousReady
      (DOTCapture.Intersections.GeneralExpression.Embedding.embedTerm term)
      (DOTCapture.Intersections.Source.embedM10Capture use)
      (DOTCapture.Intersections.Source.embedM10Ty type))
    (m10M11Agreement : previousReady.runtimeRenaming =
      DOTCaptureToManySortedFC.Acyclic.GeneralExpression.SourceErasure.compiledRenaming
        source)
    {context : Cumulative.Context
      (Embed.environment
        (DOTCapture.Intersections.GeneralExpression.Embedding.embedCtx source))
      (DOTCaptureToManySortedFC.Acyclic.Layout.sig source)}
    (cumulative : ExactEmbeddedTerm context
      (DOTCapture.Intersections.GeneralExpression.Embedding.embedTermTyping
        typing))
    (m11Stage6Agreement : RuntimeAgreement previousReady context) :
    m10Compiled.term.erase = cumulative.compiled.term.erase := by
  exact
    (DOTCaptureToManySortedFC.Intersections.GeneralExpression.CompilerConservativity.m10_m11_term_erasure_coherent
      m10Success previous m10M11Agreement).trans
      (termConservativity m11Stage6Agreement previous cumulative).erasure

end DOTCaptureToManySortedFC.RecursiveObjects.Conservativity
