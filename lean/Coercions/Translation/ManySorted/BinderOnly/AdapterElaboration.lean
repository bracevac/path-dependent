import Coercions.DOT.Captures.BinderOnly.Subtyping
import Coercions.Translation.ManySorted.BinderOnly.EvidenceElaboration
import Coercions.ManySortedFC.Administrative

/-!
# Adapter elaboration for binder-only DOT captures

Source adaptations compile derivation by derivation.  Logical cast leaves use
only `compileIncludes`; structural composition and function adaptation remain
explicit target adapters.  In particular, the function case cannot collapse
to logical type-inclusion evidence.

Quantified source adaptations recurse under an extended source context.  A
single `BoundCompiler` for the outer context does not justify lookup in that
extended context, so this initial compiler reports those two cases as
unsupported.  They can become total once layout extension supplies the
corresponding recursive bound compiler.
-/

namespace DOTCaptureToManySortedFC.BinderOnly

/-- A target adapter together with its exact translated endpoint proof. -/
structure CompiledAdapter
    {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (source target : DOTCapture.BinderOnly.Ty scope) where
  adapter : ManySortedFC.Adapter (sig context)
  typing : ManySortedFC.Adapter.HasType (translateContext context) adapter
    (translateTy context source) (translateTy context target)

/-- Compile the source adapter fragment supported by one context-local bound
compiler.

Every successful result carries its target typing derivation.  Failure is
confined to the quantified constructors, whose bodies require a
`BoundCompiler` for the extended source context. -/
def compileAdapts {scope : DOTCapture.BinderOnly.Sig}
    {context : DOTCapture.BinderOnly.Ctx scope}
    (bounds : BoundCompiler context) :
    {source target : DOTCapture.BinderOnly.Ty scope} →
    DOTCapture.BinderOnly.Adapts context source target →
      Option (CompiledAdapter context source target)
  | source, _, .identity =>
      some ⟨.identity (translateTy context source), .identity _⟩
  | _, _, .cast inclusion =>
      let compiled := compileIncludes bounds inclusion
      some ⟨.cast compiled.evidence, .cast compiled.typing⟩
  | _, _, .compose first second => do
      let firstCompiled ← compileAdapts bounds first
      let secondCompiled ← compileAdapts bounds second
      pure ⟨.compose firstCompiled.adapter secondCompiled.adapter,
        .compose firstCompiled.typing secondCompiled.typing⟩
  | _, _, .function domain codomain => do
      let domainCompiled ← compileAdapts bounds domain
      let codomainCompiled ← compileAdapts bounds codomain
      pure ⟨.function domainCompiled.adapter codomainCompiled.adapter,
        .function domainCompiled.typing codomainCompiled.typing⟩
  | _, _, .forallI _ => none
  | _, _, .existsI _ => none

namespace AdapterExamples

/-- Even reflexive components request structural function adaptation at the
source level. -/
def sourceFunction :
    DOTCapture.BinderOnly.Adapts DOTCapture.BinderOnly.Ctx.nil
      (.arr .one .one) (.arr .one .one) :=
  .function .identity .identity

/-- The exact target function adapter produced by the example. -/
def targetFunction : ManySortedFC.Adapter [] :=
  .function (.identity .one) (.identity .one)

/-- Its endpoint proof is structural as well: the final rule is
`Adapter.HasType.function`. -/
def compiledFunction :
    CompiledAdapter DOTCapture.BinderOnly.Ctx.nil
      (.arr .one .one) (.arr .one .one) where
  adapter := targetFunction
  typing := .function (.identity .one) (.identity .one)

@[simp]
theorem source_function_compiles :
    compileAdapts emptyBoundCompiler sourceFunction =
      some compiledFunction := rfl

@[simp]
theorem compiled_function_shape :
    compiledFunction.adapter =
      ManySortedFC.Adapter.function
        (.identity .one) (.identity .one) := rfl

/-- The generated eta adapter remains transparent up to the target's precise
administrative equivalence. -/
theorem compiled_function_erase_admin {runtimeScope : Nat}
    (term : ManySortedFC.Runtime.Tm runtimeScope)
    (termValue : ManySortedFC.Runtime.IsValue term) :
    ManySortedFC.Runtime.AdministrativeEq
      (compiledFunction.adapter.erase term) term :=
  ManySortedFC.Adapter.erase_admin compiledFunction.adapter term termValue

/-- A genuinely variant function conversion: the argument side is compiled
contravariantly, while the result side is compiled covariantly. -/
def variantSourceFunction :
    DOTCapture.BinderOnly.Adapts DOTCapture.BinderOnly.Ctx.nil
      (.arr .top .bot) (.arr .bot .top) :=
  .function (.cast .typeTop) (.cast .typeTop)

def variantTargetFunction : ManySortedFC.Adapter [] :=
  .function (.cast (.typeTop .bot)) (.cast (.typeTop .bot))

def compiledVariantFunction :
    CompiledAdapter DOTCapture.BinderOnly.Ctx.nil
      (.arr .top .bot) (.arr .bot .top) where
  adapter := variantTargetFunction
  typing := .function (.cast (.typeTop .bot)) (.cast (.typeTop .bot))

@[simp]
theorem variant_function_compiles_contravariantly :
    compileAdapts emptyBoundCompiler variantSourceFunction =
      some compiledVariantFunction := rfl

end AdapterExamples

end DOTCaptureToManySortedFC.BinderOnly
