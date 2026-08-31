import Coercions.DOT.Captures.BinderOnly.Subtyping
import Coercions.Translation.ManySorted.BinderOnly.IntervalMorphismElaboration
import Coercions.ManySortedFC.Administrative

/-!
# Adapter elaboration for binder-only DOT captures

Source adaptations compile derivation by derivation.  Logical cast leaves use
only `compileIncludes`; structural composition and function adaptation remain
explicit target adapters.  In particular, the function case cannot collapse
to logical type-inclusion evidence.

Quantified source adaptations recurse under the translated names-first theory
scope. The canonical context-bound compiler follows `staticSlot` at every
recursive context, so both quantified constructors elaborate totally.
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

/-- Compile every source adaptation to an explicit, typed target adapter. -/
def compileAdapts {scope : DOTCapture.BinderOnly.Sig}
    {context : DOTCapture.BinderOnly.Ctx scope}
    {source target : DOTCapture.BinderOnly.Ty scope}
    (adaptation : DOTCapture.BinderOnly.Adapts context source target) :
    CompiledAdapter context source target :=
  match adaptation with
  | .identity =>
      ⟨.identity (translateTy context source), .identity _⟩
  | .cast inclusion =>
      let compiled := compileIncludesTotal inclusion
      ⟨.cast compiled.evidence, .cast compiled.typing⟩
  | .compose first second =>
      let firstCompiled := compileAdapts first
      let secondCompiled := compileAdapts second
      ⟨.compose firstCompiled.adapter secondCompiled.adapter,
        .compose firstCompiled.typing secondCompiled.typing⟩
  | .function domain codomain =>
      let domainCompiled := compileAdapts domain
      let codomainCompiled := compileAdapts codomain
      ⟨.function domainCompiled.adapter codomainCompiled.adapter,
        .function domainCompiled.typing codomainCompiled.typing⟩
  | .captured subcapture innerAdapter =>
      let compiledSubcapture := compileIncludesTotal subcapture
      let compiledInner := compileAdapts innerAdapter
      ⟨.captured compiledSubcapture.evidence compiledInner.adapter,
        .captured compiledSubcapture.typing compiledInner.typing⟩
  | @DOTCapture.BinderOnly.Adapts.forallI _ context sort interval
      _ _ body =>
      let bodyCompiled := compileAdapts body
      ⟨.forallT (translateInterval context interval) bodyCompiled.adapter,
        .forallT bodyCompiled.typing⟩
  | @DOTCapture.BinderOnly.Adapts.forallBounds _ context sort
      sourceInterval targetInterval sourceBody targetBody bounds body =>
      match bounds with
      | @DOTCapture.BinderOnly.Interval.Entails.unbounded _ _ sort =>
          let interval :=
            DOTCapture.BinderOnly.Interval.unbounded (sort := sort)
          let constraintsCompiled := compileEntails
            (@DOTCapture.BinderOnly.Interval.Entails.unbounded
              _ context sort)
          let bodyCompiled := compileAdapts body
          ⟨.forallMorphism (translateInterval context interval)
              (translateInterval context interval)
              constraintsCompiled.morphism bodyCompiled.adapter,
            .forallMorphism constraintsCompiled.typing bodyCompiled.typing⟩
      | @DOTCapture.BinderOnly.Interval.Entails.lower _ _ _
          availableLower requiredLower lowerEvidence =>
          let sourceInterval := DOTCapture.BinderOnly.Interval.bounds
            (.some requiredLower) .none
          let targetInterval := DOTCapture.BinderOnly.Interval.bounds
            (.some availableLower) .none
          let constraintsCompiled := compileEntails
            (DOTCapture.BinderOnly.Interval.Entails.lower lowerEvidence)
          let bodyCompiled := compileAdapts body
          have bodyTyping : ManySortedFC.Adapter.HasType
              (translateContext (context.extendStatic targetInterval))
              bodyCompiled.adapter
              (translateTy (context.extendStatic sourceInterval) sourceBody)
              (translateTy (context.extendStatic targetInterval)
                targetBody) := by
            rw [translateTy_lower_required_eq_available lowerEvidence
              sourceBody]
            exact bodyCompiled.typing
          ⟨.forallMorphism (translateInterval context sourceInterval)
              (translateInterval context targetInterval)
              constraintsCompiled.morphism bodyCompiled.adapter,
            .forallMorphism constraintsCompiled.typing bodyTyping⟩
      | @DOTCapture.BinderOnly.Interval.Entails.upper _ _ _
          availableUpper requiredUpper upperEvidence =>
          let sourceInterval := DOTCapture.BinderOnly.Interval.bounds
            .none (.some requiredUpper)
          let targetInterval := DOTCapture.BinderOnly.Interval.bounds
            .none (.some availableUpper)
          let constraintsCompiled := compileEntails
            (DOTCapture.BinderOnly.Interval.Entails.upper upperEvidence)
          let bodyCompiled := compileAdapts body
          have bodyTyping : ManySortedFC.Adapter.HasType
              (translateContext (context.extendStatic targetInterval))
              bodyCompiled.adapter
              (translateTy (context.extendStatic sourceInterval) sourceBody)
              (translateTy (context.extendStatic targetInterval)
                targetBody) := by
            rw [translateTy_upper_required_eq_available upperEvidence
              sourceBody]
            exact bodyCompiled.typing
          ⟨.forallMorphism (translateInterval context sourceInterval)
              (translateInterval context targetInterval)
              constraintsCompiled.morphism bodyCompiled.adapter,
            .forallMorphism constraintsCompiled.typing bodyTyping⟩
      | @DOTCapture.BinderOnly.Interval.Entails.between _ _ _
          availableLower availableUpper requiredLower requiredUpper
          lowerEvidence upperEvidence =>
          let sourceInterval := DOTCapture.BinderOnly.Interval.bounds
            (.some requiredLower) (.some requiredUpper)
          let targetInterval := DOTCapture.BinderOnly.Interval.bounds
            (.some availableLower) (.some availableUpper)
          let constraintsCompiled := compileEntails
            (DOTCapture.BinderOnly.Interval.Entails.between
              lowerEvidence upperEvidence)
          let bodyCompiled := compileAdapts body
          have bodyTyping : ManySortedFC.Adapter.HasType
              (translateContext (context.extendStatic targetInterval))
              bodyCompiled.adapter
              (translateTy (context.extendStatic sourceInterval) sourceBody)
              (translateTy (context.extendStatic targetInterval)
                targetBody) := by
            rw [translateTy_between_required_eq_available lowerEvidence
              upperEvidence sourceBody]
            exact bodyCompiled.typing
          ⟨.forallMorphism (translateInterval context sourceInterval)
              (translateInterval context targetInterval)
              constraintsCompiled.morphism bodyCompiled.adapter,
            .forallMorphism constraintsCompiled.typing bodyTyping⟩
  | @DOTCapture.BinderOnly.Adapts.existsI _ context sort interval
      _ _ body =>
      let bodyCompiled := compileAdapts body
      ⟨.existsT (translateInterval context interval) bodyCompiled.adapter,
        .existsT bodyCompiled.typing⟩
  | @DOTCapture.BinderOnly.Adapts.existsBounds _ context sort
      sourceInterval targetInterval sourceBody targetBody bounds payload =>
      match bounds with
      | @DOTCapture.BinderOnly.Interval.Entails.unbounded _ _ sort =>
          let interval :=
            DOTCapture.BinderOnly.Interval.unbounded (sort := sort)
          let constraintsCompiled := compileEntails
            (@DOTCapture.BinderOnly.Interval.Entails.unbounded
              _ context sort)
          let payloadCompiled := compileAdapts payload
          ⟨.existsMorphism (translateInterval context interval)
              (translateInterval context interval)
              constraintsCompiled.morphism payloadCompiled.adapter,
            .existsMorphism constraintsCompiled.typing payloadCompiled.typing⟩
      | @DOTCapture.BinderOnly.Interval.Entails.lower _ _ _
          availableLower requiredLower lowerEvidence =>
          let sourceInterval := DOTCapture.BinderOnly.Interval.bounds
            (.some availableLower) .none
          let targetInterval := DOTCapture.BinderOnly.Interval.bounds
            (.some requiredLower) .none
          let constraintsCompiled := compileEntails
            (DOTCapture.BinderOnly.Interval.Entails.lower lowerEvidence)
          let payloadCompiled := compileAdapts payload
          have payloadTyping : ManySortedFC.Adapter.HasType
              (translateContext (context.extendStatic sourceInterval))
              payloadCompiled.adapter
              (translateTy (context.extendStatic sourceInterval) sourceBody)
              (translateTy (context.extendStatic targetInterval)
                targetBody) := by
            rw [translateTy_lower_required_eq_available lowerEvidence
              targetBody]
            exact payloadCompiled.typing
          ⟨.existsMorphism (translateInterval context sourceInterval)
              (translateInterval context targetInterval)
              constraintsCompiled.morphism payloadCompiled.adapter,
            .existsMorphism constraintsCompiled.typing payloadTyping⟩
      | @DOTCapture.BinderOnly.Interval.Entails.upper _ _ _
          availableUpper requiredUpper upperEvidence =>
          let sourceInterval := DOTCapture.BinderOnly.Interval.bounds
            .none (.some availableUpper)
          let targetInterval := DOTCapture.BinderOnly.Interval.bounds
            .none (.some requiredUpper)
          let constraintsCompiled := compileEntails
            (DOTCapture.BinderOnly.Interval.Entails.upper upperEvidence)
          let payloadCompiled := compileAdapts payload
          have payloadTyping : ManySortedFC.Adapter.HasType
              (translateContext (context.extendStatic sourceInterval))
              payloadCompiled.adapter
              (translateTy (context.extendStatic sourceInterval) sourceBody)
              (translateTy (context.extendStatic targetInterval)
                targetBody) := by
            rw [translateTy_upper_required_eq_available upperEvidence
              targetBody]
            exact payloadCompiled.typing
          ⟨.existsMorphism (translateInterval context sourceInterval)
              (translateInterval context targetInterval)
              constraintsCompiled.morphism payloadCompiled.adapter,
            .existsMorphism constraintsCompiled.typing payloadTyping⟩
      | @DOTCapture.BinderOnly.Interval.Entails.between _ _ _
          availableLower availableUpper requiredLower requiredUpper
          lowerEvidence upperEvidence =>
          let sourceInterval := DOTCapture.BinderOnly.Interval.bounds
            (.some availableLower) (.some availableUpper)
          let targetInterval := DOTCapture.BinderOnly.Interval.bounds
            (.some requiredLower) (.some requiredUpper)
          let constraintsCompiled := compileEntails
            (DOTCapture.BinderOnly.Interval.Entails.between
              lowerEvidence upperEvidence)
          let payloadCompiled := compileAdapts payload
          have payloadTyping : ManySortedFC.Adapter.HasType
              (translateContext (context.extendStatic sourceInterval))
              payloadCompiled.adapter
              (translateTy (context.extendStatic sourceInterval) sourceBody)
              (translateTy (context.extendStatic targetInterval)
                targetBody) := by
            rw [translateTy_between_required_eq_available lowerEvidence
              upperEvidence targetBody]
            exact payloadCompiled.typing
          ⟨.existsMorphism (translateInterval context sourceInterval)
              (translateInterval context targetInterval)
              constraintsCompiled.morphism payloadCompiled.adapter,
            .existsMorphism constraintsCompiled.typing payloadTyping⟩

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
    compileAdapts sourceFunction = compiledFunction := rfl

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
    compileAdapts variantSourceFunction = compiledVariantFunction := rfl

/-! ## Quantified adapters recurse with canonical context evidence -/

def upperTypeInterval : DOTCapture.BinderOnly.Interval .type [] :=
  .bounds .none (.some (.type .top))

def upperTypeContext :
    DOTCapture.BinderOnly.Ctx ([] ▹ .static .type) :=
  DOTCapture.BinderOnly.Ctx.nil.extendStatic upperTypeInterval

def upperReferenceHasTop :
    DOTCapture.BinderOnly.HasUpper upperTypeContext
      (.bound .here) (.type .top) :=
  .bound (lower := .none) rfl

def upperReferenceAdaptsTop :
    DOTCapture.BinderOnly.Adapts upperTypeContext
      (.ref (.bound .here)) .top :=
  .cast (.upper upperReferenceHasTop)

/-- The body cast cites the upper evidence exported by the quantified
interval, so this regression exercises recursive bound compilation rather
than only quantified identity. -/
def quantifiedForallSource :
    DOTCapture.BinderOnly.Adapts DOTCapture.BinderOnly.Ctx.nil
      (.forallI upperTypeInterval (.ref (.bound .here)))
      (.forallI upperTypeInterval .top) :=
  .forallI upperReferenceAdaptsTop

@[simp]
theorem quantified_forall_compiles_upper_slot :
    (compileAdapts quantifiedForallSource).adapter =
      ManySortedFC.Adapter.forallT
        (translateInterval DOTCapture.BinderOnly.Ctx.nil upperTypeInterval)
        (.cast (.var .here)) := rfl

def lowerTypeInterval : DOTCapture.BinderOnly.Interval .type [] :=
  .bounds (.some (.type .bot)) .none

def lowerTypeContext :
    DOTCapture.BinderOnly.Ctx ([] ▹ .static .type) :=
  DOTCapture.BinderOnly.Ctx.nil.extendStatic lowerTypeInterval

def lowerReferenceHasBottom :
    DOTCapture.BinderOnly.HasLower lowerTypeContext
      (.bound .here) (.type .bot) :=
  .bound (upper := .none) rfl

def bottomAdaptsLowerReference :
    DOTCapture.BinderOnly.Adapts lowerTypeContext
      .bot (.ref (.bound .here)) :=
  .cast (.lower lowerReferenceHasBottom)

/-- Existential congruence uses the independently present lower evidence in
its translated payload scope. -/
def quantifiedExistsSource :
    DOTCapture.BinderOnly.Adapts DOTCapture.BinderOnly.Ctx.nil
      (.existsI lowerTypeInterval .bot)
      (.existsI lowerTypeInterval (.ref (.bound .here))) :=
  .existsI bottomAdaptsLowerReference

@[simp]
theorem quantified_exists_compiles_lower_slot :
    (compileAdapts quantifiedExistsSource).adapter =
      ManySortedFC.Adapter.existsT
        (translateInterval DOTCapture.BinderOnly.Ctx.nil lowerTypeInterval)
        (.cast (.var .here)) := rfl

end AdapterExamples

end DOTCaptureToManySortedFC.BinderOnly
