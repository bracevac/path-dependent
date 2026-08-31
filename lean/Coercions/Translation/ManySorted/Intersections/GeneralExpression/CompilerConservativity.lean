import Coercions.DOT.Captures.Intersections.GeneralExpression.TypingEmbedding
import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.CompilerErasure
import Coercions.Translation.ManySorted.Intersections.GeneralExpression.Compiler
import Coercions.Translation.ManySorted.Intersections.GeneralExpression.Recursive

/-!
# M10/M11 compiler erasure conservativity

M11 changes the static representation of object signatures, so independently
generated M10 and M11 FC terms need not contain the same evidence syntax or
the same static binders.  The public compiler artifacts do support the
operational statement that matters: successful artifacts for the same source
program erase to the same runtime program.

The cross-milestone theorems below deliberately assume only compatibility of
the runtime variable projections.  They do not identify target evidence terms
or assert success of the still-separate compiler implementations.
-/

namespace DOTCaptureToManySortedFC.Intersections.GeneralExpression.CompilerConservativity

namespace M10

namespace Source

abbrev Scope := DOTCapture.Acyclic.Scope
abbrev Ctx := DOTCapture.Acyclic.Ctx
abbrev Capture := DOTCapture.Acyclic.Capture
abbrev Ty := DOTCapture.Acyclic.Ty
abbrev Value := DOTCapture.Acyclic.GeneralExpression.Value
abbrev Term := DOTCapture.Acyclic.GeneralExpression.Term

end Source

namespace Compiler

export DOTCaptureToManySortedFC.Acyclic.GeneralExpression.Compiler
  (CompiledValue CompiledTerm compilePolarizedValue? compilePolarizedTerm?)

end Compiler

namespace Runtime

export DOTCaptureToManySortedFC.Acyclic.RuntimeContext (Ready nil)

end Runtime

namespace Erasure

export DOTCaptureToManySortedFC.Acyclic.GeneralExpression.SourceErasure
  (compiledRenaming eraseValue eraseTerm)

end Erasure

end M10

namespace M11

namespace Source

abbrev Ctx := DOTCapture.Intersections.Source.Ctx
abbrev Capture := DOTCapture.Intersections.Source.Capture
abbrev Ty := DOTCapture.Intersections.Source.Ty
abbrev Value := DOTCapture.Intersections.GeneralExpression.Value
abbrev Term := DOTCapture.Intersections.GeneralExpression.Term

end Source

namespace Compiler

export DOTCaptureToManySortedFC.Intersections.GeneralExpression.Compiler
  (Ready)
export DOTCaptureToManySortedFC.Intersections.GeneralExpression.Recursive
  (CompiledValue CompiledTerm)

end Compiler

namespace Embedding

export DOTCapture.Intersections.GeneralExpression.Embedding
  (embedValue embedTerm eraseValueWith_embed eraseTermWith_embed embedCtx)

end Embedding

end M11

open ManySortedFC

/-! ## Coherence between M11 artifacts -/

/-- Two M11 value artifacts produced in the same compiler state have
identical runtime code, even if their static evidence syntax differs. -/
theorem compiledValue_erasure_coherent
    {sourceScope : M10.Source.Scope}
    {source : M11.Source.Ctx sourceScope} {targetScope : Sig}
    {ready : M11.Compiler.Ready source targetScope}
    {value : M11.Source.Value sourceScope} {type : M11.Source.Ty sourceScope}
    (first second : M11.Compiler.CompiledValue ready value type) :
    first.term.erase = second.term.erase :=
  first.exactErasure.trans second.exactErasure.symm

/-- Two M11 computation artifacts produced in the same compiler state have
identical runtime code, independently of their evidence terms. -/
theorem compiledTerm_erasure_coherent
    {sourceScope : M10.Source.Scope}
    {source : M11.Source.Ctx sourceScope} {targetScope : Sig}
    {ready : M11.Compiler.Ready source targetScope}
    {term : M11.Source.Term sourceScope}
    {use : M11.Source.Capture sourceScope} {type : M11.Source.Ty sourceScope}
    (first second : M11.Compiler.CompiledTerm ready term use type) :
    first.term.erase = second.term.erase :=
  first.exactErasure.trans second.exactErasure.symm

/-- M11 value artifacts built from distinct target contexts still erase
coherently when the contexts implement the same runtime variable projection.
The target scope is shared so both erased terms have the same index. -/
theorem compiledValue_erasure_coherent_of_runtimeRenaming_eq
    {sourceScope : M10.Source.Scope}
    {source : M11.Source.Ctx sourceScope} {targetScope : Sig}
    {firstReady secondReady : M11.Compiler.Ready source targetScope}
    {value : M11.Source.Value sourceScope} {type : M11.Source.Ty sourceScope}
    (first : M11.Compiler.CompiledValue firstReady value type)
    (second : M11.Compiler.CompiledValue secondReady value type)
    (compatible : firstReady.runtimeRenaming = secondReady.runtimeRenaming) :
    first.term.erase = second.term.erase := by
  rw [first.exactErasure, second.exactErasure]
  unfold DOTCaptureToManySortedFC.Intersections.GeneralExpression.Compiler.Ready.eraseValue
  rw [compatible]

/-- Computation counterpart of
`compiledValue_erasure_coherent_of_runtimeRenaming_eq`. -/
theorem compiledTerm_erasure_coherent_of_runtimeRenaming_eq
    {sourceScope : M10.Source.Scope}
    {source : M11.Source.Ctx sourceScope} {targetScope : Sig}
    {firstReady secondReady : M11.Compiler.Ready source targetScope}
    {term : M11.Source.Term sourceScope}
    {use : M11.Source.Capture sourceScope} {type : M11.Source.Ty sourceScope}
    (first : M11.Compiler.CompiledTerm firstReady term use type)
    (second : M11.Compiler.CompiledTerm secondReady term use type)
    (compatible : firstReady.runtimeRenaming = secondReady.runtimeRenaming) :
    first.term.erase = second.term.erase := by
  rw [first.exactErasure, second.exactErasure]
  unfold DOTCaptureToManySortedFC.Intersections.GeneralExpression.Compiler.Ready.eraseTerm
  rw [compatible]

/-! ## Conditional conservativity over successful M10 compilation -/

/-- A successful M10 polarized value compilation and any M11 artifact for
its cumulative embedding erase identically, provided the two compiler states
project source variables to the same runtime coordinates. -/
theorem m10_m11_value_erasure_coherent
    {scope : M10.Source.Scope} {context : M10.Source.Ctx scope}
    {m10Ready : M10.Runtime.Ready context}
    {value : M10.Source.Value scope} {type : M10.Source.Ty scope}
    {typing : DOTCapture.Acyclic.GeneralExpression.Value.HasType
      context value type}
    {m10Compiled : M10.Compiler.CompiledValue m10Ready value type}
    (m10Success : M10.Compiler.compilePolarizedValue? m10Ready typing =
      some m10Compiled)
    {m11Ready : M11.Compiler.Ready (M11.Embedding.embedCtx context)
      (DOTCaptureToManySortedFC.Acyclic.Layout.sig context)}
    (m11Compiled : M11.Compiler.CompiledValue m11Ready
      (M11.Embedding.embedValue value)
      (DOTCapture.Intersections.Source.embedM10Ty type))
    (compatible : m11Ready.runtimeRenaming =
      M10.Erasure.compiledRenaming context) :
    m10Compiled.term.erase = m11Compiled.term.erase := by
  calc
    m10Compiled.term.erase = M10.Erasure.eraseValue context value :=
      DOTCaptureToManySortedFC.Acyclic.GeneralExpression.CompilerErasure.compilePolarizedValue_erase
        m10Success
    _ = m11Ready.eraseValue (M11.Embedding.embedValue value) := by
      unfold M10.Erasure.eraseValue
      unfold DOTCaptureToManySortedFC.Intersections.GeneralExpression.Compiler.Ready.eraseValue
      rw [compatible]
      exact (M11.Embedding.eraseValueWith_embed
        (M10.Erasure.compiledRenaming context) value).symm
    _ = m11Compiled.term.erase := m11Compiled.exactErasure.symm

/-- Computation counterpart of `m10_m11_value_erasure_coherent`.  This is
the strongest public conservativity statement that does not identify the two
compilers' private evidence-generation traces. -/
theorem m10_m11_term_erasure_coherent
    {scope : M10.Source.Scope} {context : M10.Source.Ctx scope}
    {m10Ready : M10.Runtime.Ready context}
    {term : M10.Source.Term scope} {use : M10.Source.Capture scope}
    {type : M10.Source.Ty scope}
    {typing : DOTCapture.Acyclic.GeneralExpression.Term.HasType
      context term use type}
    {m10Compiled : M10.Compiler.CompiledTerm m10Ready term use type}
    (m10Success : M10.Compiler.compilePolarizedTerm? m10Ready typing =
      some m10Compiled)
    {m11Ready : M11.Compiler.Ready (M11.Embedding.embedCtx context)
      (DOTCaptureToManySortedFC.Acyclic.Layout.sig context)}
    (m11Compiled : M11.Compiler.CompiledTerm m11Ready
      (M11.Embedding.embedTerm term)
      (DOTCapture.Intersections.Source.embedM10Capture use)
      (DOTCapture.Intersections.Source.embedM10Ty type))
    (compatible : m11Ready.runtimeRenaming =
      M10.Erasure.compiledRenaming context) :
    m10Compiled.term.erase = m11Compiled.term.erase := by
  calc
    m10Compiled.term.erase = M10.Erasure.eraseTerm context term :=
      DOTCaptureToManySortedFC.Acyclic.GeneralExpression.CompilerErasure.compilePolarizedTerm_erase
        m10Success
    _ = m11Ready.eraseTerm (M11.Embedding.embedTerm term) := by
      unfold M10.Erasure.eraseTerm
      unfold DOTCaptureToManySortedFC.Intersections.GeneralExpression.Compiler.Ready.eraseTerm
      rw [compatible]
      exact (M11.Embedding.eraseTermWith_embed
        (M10.Erasure.compiledRenaming context) term).symm
    _ = m11Compiled.term.erase := m11Compiled.exactErasure.symm

/-! ## Closed specialization -/

/-- Canonical empty M11 compiler state.  It is intentionally public so the
closed regression module can share exactly this runtime projection. -/
def emptyReady : M11.Compiler.Ready
    (M11.Embedding.embedCtx
      (DOTCapture.Acyclic.Ctx.nil : M10.Source.Ctx 0)) [] where
  layout := DOTCaptureToManySortedFC.Intersections.Preparation.emptyLayout []
  target := Ctx.nil

@[simp]
theorem emptyReady_runtimeRenaming :
    emptyReady.runtimeRenaming =
      M10.Erasure.compiledRenaming
        (DOTCapture.Acyclic.Ctx.nil : M10.Source.Ctx 0) := by
  funext name
  nomatch name

/-- Closed successful M10 and M11 value artifacts erase to the same runtime
term without an extra compatibility premise. -/
theorem closed_m10_m11_value_erasure_coherent
    {value : M10.Source.Value 0} {type : M10.Source.Ty 0}
    {typing : DOTCapture.Acyclic.GeneralExpression.Value.HasType
      DOTCapture.Acyclic.Ctx.nil value type}
    {m10Compiled : M10.Compiler.CompiledValue M10.Runtime.nil value type}
    (m10Success : M10.Compiler.compilePolarizedValue? M10.Runtime.nil typing =
      some m10Compiled)
    (m11Compiled : M11.Compiler.CompiledValue emptyReady
      (M11.Embedding.embedValue value)
      (DOTCapture.Intersections.Source.embedM10Ty type)) :
    m10Compiled.term.erase = m11Compiled.term.erase :=
  m10_m11_value_erasure_coherent m10Success m11Compiled
    emptyReady_runtimeRenaming

/-- Closed computation specialization used by M10/M11 compiler regressions. -/
theorem closed_m10_m11_term_erasure_coherent
    {term : M10.Source.Term 0} {use : M10.Source.Capture 0}
    {type : M10.Source.Ty 0}
    {typing : DOTCapture.Acyclic.GeneralExpression.Term.HasType
      DOTCapture.Acyclic.Ctx.nil term use type}
    {m10Compiled : M10.Compiler.CompiledTerm M10.Runtime.nil term use type}
    (m10Success : M10.Compiler.compilePolarizedTerm? M10.Runtime.nil typing =
      some m10Compiled)
    (m11Compiled : M11.Compiler.CompiledTerm emptyReady
      (M11.Embedding.embedTerm term)
      (DOTCapture.Intersections.Source.embedM10Capture use)
      (DOTCapture.Intersections.Source.embedM10Ty type)) :
    m10Compiled.term.erase = m11Compiled.term.erase :=
  m10_m11_term_erasure_coherent m10Success m11Compiled
    emptyReady_runtimeRenaming

end DOTCaptureToManySortedFC.Intersections.GeneralExpression.CompilerConservativity
