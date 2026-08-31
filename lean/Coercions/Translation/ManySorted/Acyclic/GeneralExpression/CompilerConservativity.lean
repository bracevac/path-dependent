import Coercions.DOT.Captures.Acyclic.GeneralExpression.Embedding
import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.SourceErasure
import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.Compiler
import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.CompilerErasure
import Coercions.Translation.ManySorted.Acyclic.TermTranslationErasure

/-!
# Conservativity over the value-MNF compiler core

The general-expression source embeds the earlier value-MNF source without
changing its static judgments.  This module establishes the corresponding
translation-layer compatibility: direct source erasure commutes with that
embedding, a core artifact can be reindexed into a surface artifact without
changing any target field, and independently successful compiler outputs
agree on their exact translated indices and erased target program.

The two compilers intentionally hide separate dependent evidence and binder
finishing pipelines.  Their public APIs do not expose enough of those private
traces to identify the emitted evidence syntax or prove success reflection
without widening those APIs, so this module does not assert either fact.
-/

namespace DOTCaptureToManySortedFC.Acyclic.GeneralExpression.CompilerConservativity

namespace Source

export DOTCapture.Acyclic
  (Scope Capture Ty Ctx Value Term)

namespace Value
export DOTCapture.Acyclic.Value (HasType)
end Value

namespace Term
export DOTCapture.Acyclic.Term (HasType)
end Term

end Source

namespace Embedding

export DOTCapture.Acyclic.GeneralExpression.Embedding
  (embedValue embedTerm embedValueTyping embedTermTyping)

end Embedding

namespace CoreCompiler

export DOTCaptureToManySortedFC.Acyclic.ValueTranslation
  (CompiledValue CompiledTerm compileValue? compileTerm?)

end CoreCompiler

namespace SurfaceCompiler

export DOTCaptureToManySortedFC.Acyclic.GeneralExpression.Compiler
  (CompiledValue CompiledTerm compileValue? compileTerm?
    compilePolarizedTerm?)

end SurfaceCompiler

namespace Runtime

export DOTCaptureToManySortedFC.Acyclic.RuntimeContext (Ready)

end Runtime

/-! ## Independent source erasure -/

namespace CoreErasure

export DOTCaptureToManySortedFC.Acyclic.SourceErasure
  (Renaming eraseValueWith eraseTermWith eraseValue eraseTerm)

end CoreErasure

namespace SurfaceErasure

export DOTCapture.Acyclic.GeneralExpression.Erasure
  (eraseValueWith eraseTermWith)

export DOTCaptureToManySortedFC.Acyclic.GeneralExpression.SourceErasure
  (eraseValue eraseTerm)

end SurfaceErasure

mutual

/-- Generalized direct erasure of an embedded value is exactly the established
direct erasure of the value-MNF value. -/
@[simp]
theorem eraseValueWith_embed {scope runtimeScope : Nat}
    (rho : CoreErasure.Renaming scope runtimeScope)
    (value : Source.Value scope) :
    SurfaceErasure.eraseValueWith rho (Embedding.embedValue value) =
      CoreErasure.eraseValueWith rho value :=
  match value with
  | .var _ => rfl
  | .unit => rfl
  | .lam _domain _codomain body =>
      congrArg ManySortedFC.Runtime.Tm.lam
        (eraseTermWith_embed
          (DOTCaptureToManySortedFC.Acyclic.SourceErasure.Renaming.lift rho)
          body)
  | .object _signature _typeWitness _captureWitness payload =>
      eraseValueWith_embed rho payload

/-- Generalized direct erasure commutes with the term embedding exactly. -/
@[simp]
theorem eraseTermWith_embed {scope runtimeScope : Nat}
    (rho : CoreErasure.Renaming scope runtimeScope)
    (term : Source.Term scope) :
    SurfaceErasure.eraseTermWith rho (Embedding.embedTerm term) =
      CoreErasure.eraseTermWith rho term :=
  match term with
  | .ret value => eraseValueWith_embed rho value
  | .select _receiver .v => rfl
  | .app function argument => by
      simp only [Embedding.embedTerm,
        DOTCapture.Acyclic.GeneralExpression.Erasure.eraseTermWith_app,
        DOTCapture.Acyclic.GeneralExpression.Erasure.eraseTermWith_ret,
        CoreErasure.eraseTermWith, eraseValueWith_embed]
  | .let' _result rhs body => by
      change ManySortedFC.Runtime.Tm.let'
          (SurfaceErasure.eraseTermWith rho (Embedding.embedTerm rhs))
          (SurfaceErasure.eraseTermWith
            (DOTCapture.Acyclic.GeneralExpression.Erasure.Renaming.lift rho)
            (Embedding.embedTerm body)) =
        ManySortedFC.Runtime.Tm.let' (CoreErasure.eraseTermWith rho rhs)
          (CoreErasure.eraseTermWith
            (DOTCaptureToManySortedFC.Acyclic.SourceErasure.Renaming.lift rho)
            body)
      rw [eraseTermWith_embed rho rhs]
      have lifts :
          DOTCapture.Acyclic.GeneralExpression.Erasure.Renaming.lift rho =
            DOTCaptureToManySortedFC.Acyclic.SourceErasure.Renaming.lift rho := by
        funext index
        cases index <;> rfl
      rw [lifts]
      rw [eraseTermWith_embed
        (DOTCaptureToManySortedFC.Acyclic.SourceErasure.Renaming.lift rho)
        body]

end

/-- Layout-indexed erasure agrees for embedded values. -/
@[simp]
theorem eraseValue_embed {scope : Source.Scope} (context : Source.Ctx scope)
    (value : Source.Value scope) :
    SurfaceErasure.eraseValue context (Embedding.embedValue value) =
      CoreErasure.eraseValue context value :=
  eraseValueWith_embed
    (DOTCaptureToManySortedFC.Acyclic.SourceErasure.compiledRenaming context)
    value

/-- Layout-indexed erasure agrees for embedded computations. -/
@[simp]
theorem eraseTerm_embed {scope : Source.Scope} (context : Source.Ctx scope)
    (term : Source.Term scope) :
    SurfaceErasure.eraseTerm context (Embedding.embedTerm term) =
      CoreErasure.eraseTerm context term :=
  eraseTermWith_embed
    (DOTCaptureToManySortedFC.Acyclic.SourceErasure.compiledRenaming context)
    term

/-! ## Zero-cost artifact reindexing -/

/-- Reindex a core value artifact along the source embedding.  All target
fields, including the generated term, are retained literally. -/
def embedCompiledValue {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {value : Source.Value scope} {type : Source.Ty scope}
    (compiled : CoreCompiler.CompiledValue ready value type) :
    SurfaceCompiler.CompiledValue ready (Embedding.embedValue value) type :=
  { targetType := compiled.targetType
    typeTranslated := compiled.typeTranslated
    term := compiled.term
    isValue := compiled.isValue
    typing := compiled.typing }

/-- Reindex a core computation artifact.  Its source typing certificate is
embedded; every independently checkable target field is retained literally. -/
def embedCompiledTerm {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {term : Source.Term scope} {use : Source.Capture scope}
    {type : Source.Ty scope}
    (compiled : CoreCompiler.CompiledTerm ready term use type) :
    SurfaceCompiler.CompiledTerm ready (Embedding.embedTerm term) use type :=
  { sourceTyping := Embedding.embedTermTyping compiled.sourceTyping
    targetUse := compiled.targetUse
    targetType := compiled.targetType
    useTranslated := compiled.useTranslated
    typeTranslated := compiled.typeTranslated
    term := compiled.term
    typing := compiled.typing }

@[simp]
theorem embedCompiledValue_term {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {value : Source.Value scope} {type : Source.Ty scope}
    (compiled : CoreCompiler.CompiledValue ready value type) :
    (embedCompiledValue compiled).term = compiled.term := rfl

@[simp]
theorem embedCompiledValue_targetType {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {value : Source.Value scope} {type : Source.Ty scope}
    (compiled : CoreCompiler.CompiledValue ready value type) :
    (embedCompiledValue compiled).targetType = compiled.targetType := rfl

@[simp]
theorem embedCompiledTerm_term {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {term : Source.Term scope} {use : Source.Capture scope}
    {type : Source.Ty scope}
    (compiled : CoreCompiler.CompiledTerm ready term use type) :
    (embedCompiledTerm compiled).term = compiled.term := rfl

@[simp]
theorem embedCompiledTerm_targetUse {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {term : Source.Term scope} {use : Source.Capture scope}
    {type : Source.Ty scope}
    (compiled : CoreCompiler.CompiledTerm ready term use type) :
    (embedCompiledTerm compiled).targetUse = compiled.targetUse := rfl

@[simp]
theorem embedCompiledTerm_targetType {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {term : Source.Term scope} {use : Source.Capture scope}
    {type : Source.Ty scope}
    (compiled : CoreCompiler.CompiledTerm ready term use type) :
    (embedCompiledTerm compiled).targetType = compiled.targetType := rfl

/-! ## Agreement of successful artifacts -/

/-- The strongest compiler-independent agreement available through the
public compiler APIs for values: exact translated type index and exact erased
target program. -/
structure ValueArtifactsAgree {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {value : Source.Value scope} {type : Source.Ty scope}
    (core : CoreCompiler.CompiledValue ready value type)
    (surface : SurfaceCompiler.CompiledValue ready
      (Embedding.embedValue value) type) : Prop where
  targetType : core.targetType = surface.targetType
  erasedTerm : core.term.erase = surface.term.erase

/-- Successful value artifacts agree on every independently translated index
and on their complete runtime program. -/
theorem successfulValue_artifactsAgree {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {value : Source.Value scope} {type : Source.Ty scope}
    {typing : Source.Value.HasType context value type}
    {core : CoreCompiler.CompiledValue ready value type}
    {surface : SurfaceCompiler.CompiledValue ready
      (Embedding.embedValue value) type}
    (coreSuccess : CoreCompiler.compileValue? ready typing = some core)
    (surfaceSuccess : SurfaceCompiler.compileValue? ready
      (Embedding.embedValueTyping typing) = some surface) :
    ValueArtifactsAgree core surface := by
  refine
    { targetType := StaticTranslation.TranslatesTy.functional
        core.typeTranslated surface.typeTranslated
      erasedTerm := ?_ }
  calc
    core.term.erase = CoreErasure.eraseValue context value :=
      DOTCaptureToManySortedFC.Acyclic.ValueTranslationErasure.compileValue_erase
        coreSuccess
    _ = SurfaceErasure.eraseValue context (Embedding.embedValue value) :=
      (eraseValue_embed context value).symm
    _ = surface.term.erase :=
      (DOTCaptureToManySortedFC.Acyclic.GeneralExpression.CompilerErasure.compileValue_erase
        surfaceSuccess).symm

/-- Successful term artifacts agree on both translated indices and on their
complete runtime program. -/
structure TermArtifactsAgree {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {term : Source.Term scope} {use : Source.Capture scope}
    {type : Source.Ty scope}
    (core : CoreCompiler.CompiledTerm ready term use type)
    (surface : SurfaceCompiler.CompiledTerm ready
      (Embedding.embedTerm term) use type) : Prop where
  targetUse : core.targetUse = surface.targetUse
  targetType : core.targetType = surface.targetType
  erasedTerm : core.term.erase = surface.term.erase

/-- Conditional compiler conservativity for computations.  Given successful
outputs from both derivation-directed compilers, their translated capture and
type indices are literally equal and their erased target terms are literally
equal. -/
theorem successfulTerm_artifactsAgree {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {term : Source.Term scope} {use : Source.Capture scope}
    {type : Source.Ty scope}
    {typing : Source.Term.HasType context term use type}
    {core : CoreCompiler.CompiledTerm ready term use type}
    {surface : SurfaceCompiler.CompiledTerm ready
      (Embedding.embedTerm term) use type}
    (coreSuccess : CoreCompiler.compileTerm? ready typing = some core)
    (surfaceSuccess : SurfaceCompiler.compileTerm? ready
      (Embedding.embedTermTyping typing) = some surface) :
    TermArtifactsAgree core surface := by
  refine
    { targetUse := StaticTranslation.TranslatesCapture.functional
        core.useTranslated surface.useTranslated
      targetType := StaticTranslation.TranslatesTy.functional
        core.typeTranslated surface.typeTranslated
      erasedTerm := ?_ }
  calc
    core.term.erase = CoreErasure.eraseTerm context term :=
      DOTCaptureToManySortedFC.Acyclic.TermTranslationErasure.compileTerm_erase
        coreSuccess
    _ = SurfaceErasure.eraseTerm context (Embedding.embedTerm term) :=
      (eraseTerm_embed context term).symm
    _ = surface.term.erase :=
      (DOTCaptureToManySortedFC.Acyclic.GeneralExpression.CompilerErasure.compileTerm_erase
        surfaceSuccess).symm

/-! ## Agreement with the polarized extension -/

/-- The original general-expression compiler and its polarized extension
agree on all public target indices and on the complete runtime program
whenever both accept the same source derivation.  The statement deliberately
does not identify proof syntax hidden by their dependent result types. -/
structure DirectPolarizedTermArtifactsAgree {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {term : DOTCapture.Acyclic.GeneralExpression.Term scope}
    {use : Source.Capture scope} {type : Source.Ty scope}
    (direct : SurfaceCompiler.CompiledTerm ready term use type)
    (polarized : SurfaceCompiler.CompiledTerm ready term use type) : Prop where
  targetUse : direct.targetUse = polarized.targetUse
  targetType : direct.targetType = polarized.targetType
  erasedTerm : direct.term.erase = polarized.term.erase

/-- Conditional conservativity over the pre-existing direct compiler.  A
program accepted by both entry points keeps its translated capture,
translated type, and exact erased runtime code. -/
theorem successfulDirectPolarizedTerm_artifactsAgree {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {term : DOTCapture.Acyclic.GeneralExpression.Term scope}
    {use : Source.Capture scope} {type : Source.Ty scope}
    {typing : DOTCapture.Acyclic.GeneralExpression.Term.HasType context term
      use type}
    {direct polarized : SurfaceCompiler.CompiledTerm ready term use type}
    (directSuccess : SurfaceCompiler.compileTerm? ready typing = some direct)
    (polarizedSuccess : SurfaceCompiler.compilePolarizedTerm? ready typing =
      some polarized) :
    DirectPolarizedTermArtifactsAgree direct polarized := by
  refine
    { targetUse := StaticTranslation.TranslatesCapture.functional
        direct.useTranslated polarized.useTranslated
      targetType := StaticTranslation.TranslatesTy.functional
        direct.typeTranslated polarized.typeTranslated
      erasedTerm := ?_ }
  calc
    direct.term.erase = SurfaceErasure.eraseTerm context term :=
      DOTCaptureToManySortedFC.Acyclic.GeneralExpression.CompilerErasure.compileTerm_erase
        directSuccess
    _ = polarized.term.erase :=
      (DOTCaptureToManySortedFC.Acyclic.GeneralExpression.CompilerErasure.compilePolarizedTerm_erase
        polarizedSuccess).symm

end DOTCaptureToManySortedFC.Acyclic.GeneralExpression.CompilerConservativity
