import Coercions.DOT.Captures.BinderOnly.IntervalEntailment
import Coercions.Translation.ManySorted.BinderOnly.ContextEvidence
import Coercions.ManySortedFC.TheoryMorphismChecker

/-!
# Interval-entailment elaboration

Same-shape source interval entailments compile to identity-on-symbols target
theory morphisms.  The translated available interval supplies the context in
which each required endpoint certificate is checked.
-/

namespace DOTCaptureToManySortedFC.BinderOnly

/-- A target theory morphism paired with its declarative validation proof. -/
structure CompiledIntervalMorphism
    {scope : ManySortedFC.Sig} (context : ManySortedFC.Ctx scope)
    {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation}
    (source target : ManySortedFC.Theory scope symbols relations) where
  morphism : ManySortedFC.TheoryMorphism source target
  typing : ManySortedFC.TheoryMorphism.HasType context morphism

/-- The exact target result type selected by a same-shape source entailment.
The dependency on the derivation exposes the common relation list without
transporting either translated endpoint theory. -/
def EntailmentCompilation
    {scope : DOTCapture.BinderOnly.Sig}
    {context : DOTCapture.BinderOnly.Ctx scope}
    {sort : DOTCapture.BinderOnly.StaticSort}
    {available required : DOTCapture.BinderOnly.Interval sort scope}
    (entailment : DOTCapture.BinderOnly.Interval.Entails
      context available required) : Type :=
  match entailment with
  | .unbounded =>
      CompiledIntervalMorphism (translateContext context)
        (translateInterval context
          (DOTCapture.BinderOnly.Interval.unbounded (sort := sort)))
        (translateInterval context
          (DOTCapture.BinderOnly.Interval.unbounded (sort := sort)))
  | @DOTCapture.BinderOnly.Interval.Entails.lower _ _ _
      availableLower requiredLower _ =>
      CompiledIntervalMorphism (translateContext context)
        (translateInterval context
          (.bounds (.some availableLower) .none))
        (translateInterval context
          (.bounds (.some requiredLower) .none))
  | @DOTCapture.BinderOnly.Interval.Entails.upper _ _ _
      availableUpper requiredUpper _ =>
      CompiledIntervalMorphism (translateContext context)
        (translateInterval context
          (.bounds .none (.some availableUpper)))
        (translateInterval context
          (.bounds .none (.some requiredUpper)))
  | @DOTCapture.BinderOnly.Interval.Entails.between _ _ _
      availableLower availableUpper requiredLower requiredUpper _ _ =>
      CompiledIntervalMorphism (translateContext context)
        (translateInterval context
          (.bounds (.some availableLower) (.some availableUpper)))
        (translateInterval context
          (.bounds (.some requiredLower) (.some requiredUpper)))

/-- The exact identity-renaming agreement selected by a same-shape interval
entailment.  Its result depends on the derivation because target signatures
retain the interval's relation list as an index. -/
def EntailmentRenameAgreement
    {scope : DOTCapture.BinderOnly.Sig}
    {context : DOTCapture.BinderOnly.Ctx scope}
    {sort : DOTCapture.BinderOnly.StaticSort}
    {available required : DOTCapture.BinderOnly.Interval sort scope}
    (entailment : DOTCapture.BinderOnly.Interval.Entails
      context available required) : Prop :=
  match entailment with
  | .unbounded =>
      RenameAgreement
        (context.extendStatic
          (DOTCapture.BinderOnly.Interval.unbounded (sort := sort)))
        (context.extendStatic
          (DOTCapture.BinderOnly.Interval.unbounded (sort := sort)))
        DOTCapture.BinderOnly.Rename.id ManySortedFC.Rename.id
  | @DOTCapture.BinderOnly.Interval.Entails.lower _ _ _
      availableLower requiredLower _ =>
      RenameAgreement
        (context.extendStatic (.bounds (.some availableLower) .none))
        (context.extendStatic (.bounds (.some requiredLower) .none))
        DOTCapture.BinderOnly.Rename.id ManySortedFC.Rename.id
  | @DOTCapture.BinderOnly.Interval.Entails.upper _ _ _
      availableUpper requiredUpper _ =>
      RenameAgreement
        (context.extendStatic (.bounds .none (.some availableUpper)))
        (context.extendStatic (.bounds .none (.some requiredUpper)))
        DOTCapture.BinderOnly.Rename.id ManySortedFC.Rename.id
  | @DOTCapture.BinderOnly.Interval.Entails.between _ _ _
      availableLower availableUpper requiredLower requiredUpper _ _ =>
      RenameAgreement
        (context.extendStatic
          (.bounds (.some availableLower) (.some availableUpper)))
        (context.extendStatic
          (.bounds (.some requiredLower) (.some requiredUpper)))
        DOTCapture.BinderOnly.Rename.id ManySortedFC.Rename.id

/-- Endpoint expressions do not affect generated coordinates, so identity
renamings agree between the two contexts of every same-shape entailment. -/
def sameShapeAgreement
    {scope : DOTCapture.BinderOnly.Sig}
    {context : DOTCapture.BinderOnly.Ctx scope}
    {sort : DOTCapture.BinderOnly.StaticSort}
    {available required : DOTCapture.BinderOnly.Interval sort scope}
    (entailment : DOTCapture.BinderOnly.Interval.Entails
      context available required) :
    EntailmentRenameAgreement entailment :=
  match entailment with
  | .unbounded => RenameAgreement.identity _
  | .lower _ =>
      { term := by intro index; cases index <;> rfl
        static := by
          intro otherSort index
          cases index with
          | here =>
              simp only [DOTCapture.BinderOnly.Ctx.extendStatic,
                DOTCapture.BinderOnly.Rename.id_var, staticSlot]
              exact (ManySortedTranslation.StaticSlot.rename_id _).symm
          | there older =>
              simp only [DOTCapture.BinderOnly.Ctx.extendStatic,
                DOTCapture.BinderOnly.Rename.id_var, staticSlot,
                ManySortedTranslation.StaticSlot.rename_comp]
              rfl }
  | .upper _ =>
      { term := by intro index; cases index <;> rfl
        static := by
          intro otherSort index
          cases index with
          | here =>
              simp only [DOTCapture.BinderOnly.Ctx.extendStatic,
                DOTCapture.BinderOnly.Rename.id_var, staticSlot]
              exact (ManySortedTranslation.StaticSlot.rename_id _).symm
          | there older =>
              simp only [DOTCapture.BinderOnly.Ctx.extendStatic,
                DOTCapture.BinderOnly.Rename.id_var, staticSlot,
                ManySortedTranslation.StaticSlot.rename_comp]
              rfl }
  | .between _ _ =>
      { term := by intro index; cases index <;> rfl
        static := by
          intro otherSort index
          cases index with
          | here =>
              simp only [DOTCapture.BinderOnly.Ctx.extendStatic,
                DOTCapture.BinderOnly.Rename.id_var, staticSlot]
              exact (ManySortedTranslation.StaticSlot.rename_id _).symm
          | there older =>
              simp only [DOTCapture.BinderOnly.Ctx.extendStatic,
                DOTCapture.BinderOnly.Rename.id_var, staticSlot,
                ManySortedTranslation.StaticSlot.rename_comp]
              rfl }

/-- Lower-only endpoint values do not affect type translation below the
generated static scope. -/
theorem translateTy_lower_required_eq_available
    {scope : DOTCapture.BinderOnly.Sig}
    {context : DOTCapture.BinderOnly.Ctx scope}
    {sort : DOTCapture.BinderOnly.StaticSort}
    {availableLower requiredLower :
      DOTCapture.BinderOnly.StaticExpr sort scope}
    (lowerEvidence : DOTCapture.BinderOnly.Includes
      (context.extendStatic (.bounds (.some availableLower) .none))
      requiredLower.weaken
      (DOTCapture.BinderOnly.StaticExpr.bound
        (.here : DOTCapture.BinderOnly.BVar
          (scope ▹ .static sort) (.static sort))))
    (type : DOTCapture.BinderOnly.Ty (scope ▹ .static sort)) :
    translateTy
      (context.extendStatic (.bounds (.some requiredLower) .none)) type =
      translateTy
        (context.extendStatic (.bounds (.some availableLower) .none)) type :=
  calc
    translateTy
        (context.extendStatic (.bounds (.some requiredLower) .none)) type =
      (translateTy
        (context.extendStatic (.bounds (.some availableLower) .none))
        type).rename (ManySortedFC.Rename.id (scope :=
          sig (context.extendStatic
            (.bounds (.some availableLower) .none)))) := by
      simpa only [DOTCapture.BinderOnly.Ty.rename_id] using
        translateTy_rename
          (sameShapeAgreement
            (DOTCapture.BinderOnly.Interval.Entails.lower lowerEvidence)) type
    _ = translateTy
        (context.extendStatic (.bounds (.some availableLower) .none)) type :=
      ManySortedFC.Ty.rename_id _

/-- Upper-only endpoint values do not affect type translation below the
generated static scope. -/
theorem translateTy_upper_required_eq_available
    {scope : DOTCapture.BinderOnly.Sig}
    {context : DOTCapture.BinderOnly.Ctx scope}
    {sort : DOTCapture.BinderOnly.StaticSort}
    {availableUpper requiredUpper :
      DOTCapture.BinderOnly.StaticExpr sort scope}
    (upperEvidence : DOTCapture.BinderOnly.Includes
      (context.extendStatic (.bounds .none (.some availableUpper)))
      (DOTCapture.BinderOnly.StaticExpr.bound
        (.here : DOTCapture.BinderOnly.BVar
          (scope ▹ .static sort) (.static sort)))
      requiredUpper.weaken)
    (type : DOTCapture.BinderOnly.Ty (scope ▹ .static sort)) :
    translateTy
      (context.extendStatic (.bounds .none (.some requiredUpper))) type =
      translateTy
        (context.extendStatic (.bounds .none (.some availableUpper))) type :=
  calc
    translateTy
        (context.extendStatic (.bounds .none (.some requiredUpper))) type =
      (translateTy
        (context.extendStatic (.bounds .none (.some availableUpper)))
        type).rename (ManySortedFC.Rename.id (scope :=
          sig (context.extendStatic
            (.bounds .none (.some availableUpper))))) := by
      simpa only [DOTCapture.BinderOnly.Ty.rename_id] using
        translateTy_rename
          (sameShapeAgreement
            (DOTCapture.BinderOnly.Interval.Entails.upper upperEvidence)) type
    _ = translateTy
        (context.extendStatic (.bounds .none (.some availableUpper))) type :=
      ManySortedFC.Ty.rename_id _

/-- Two-sided endpoint values do not affect type translation below the
generated static scope. -/
theorem translateTy_between_required_eq_available
    {scope : DOTCapture.BinderOnly.Sig}
    {context : DOTCapture.BinderOnly.Ctx scope}
    {sort : DOTCapture.BinderOnly.StaticSort}
    {availableLower availableUpper requiredLower requiredUpper :
      DOTCapture.BinderOnly.StaticExpr sort scope}
    (lowerEvidence : DOTCapture.BinderOnly.Includes
      (context.extendStatic
        (.bounds (.some availableLower) (.some availableUpper)))
      requiredLower.weaken
      (DOTCapture.BinderOnly.StaticExpr.bound
        (.here : DOTCapture.BinderOnly.BVar
          (scope ▹ .static sort) (.static sort))))
    (upperEvidence : DOTCapture.BinderOnly.Includes
      (context.extendStatic
        (.bounds (.some availableLower) (.some availableUpper)))
      (DOTCapture.BinderOnly.StaticExpr.bound
        (.here : DOTCapture.BinderOnly.BVar
          (scope ▹ .static sort) (.static sort)))
      requiredUpper.weaken)
    (type : DOTCapture.BinderOnly.Ty (scope ▹ .static sort)) :
    translateTy
      (context.extendStatic
        (.bounds (.some requiredLower) (.some requiredUpper))) type =
      translateTy
        (context.extendStatic
          (.bounds (.some availableLower) (.some availableUpper))) type :=
  calc
    translateTy
        (context.extendStatic
          (.bounds (.some requiredLower) (.some requiredUpper))) type =
      (translateTy
        (context.extendStatic
          (.bounds (.some availableLower) (.some availableUpper)))
        type).rename (ManySortedFC.Rename.id (scope :=
          sig (context.extendStatic
            (.bounds (.some availableLower) (.some availableUpper))))) := by
      simpa only [DOTCapture.BinderOnly.Ty.rename_id] using
        translateTy_rename
          (sameShapeAgreement
            (DOTCapture.BinderOnly.Interval.Entails.between
              lowerEvidence upperEvidence)) type
    _ = translateTy
        (context.extendStatic
          (.bounds (.some availableLower) (.some availableUpper))) type :=
      ManySortedFC.Ty.rename_id _

/-- Translating an outer endpoint below a source static binder agrees with
target weakening below the generated symbol and complete evidence block. -/
private theorem translateEndpointUnderInterval
    {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (interval : DOTCapture.BinderOnly.Interval sort scope)
    (endpoint : DOTCapture.BinderOnly.StaticExpr sort scope) :
    translateExpr (context.extendStatic interval) endpoint.weaken =
      ((translateExpr context endpoint).weaken).rename
        (ManySortedFC.Rename.weakenMany
          (ManySortedFC.SymbolScope (sig context) [translateSort sort])
          (ManySortedFC.evidenceKinds (intervalRelations interval))) := by
  calc
    _ = (translateExpr context endpoint).rename
        (extendRename context
          (DOTCapture.BinderOnly.Binding.static interval)) :=
      translateExpr_weaken context
        (DOTCapture.BinderOnly.Binding.static interval) endpoint
    _ = _ := by
      simp [extendRename, ManySortedFC.StaticExpr.weaken,
        ManySortedFC.Rename.weakenStatic,
        ManySortedFC.Rename.weakenSymbols,
        ManySortedFC.Rename.weakenMany,
        ManySortedFC.symbolKinds, ManySortedFC.StaticExpr.rename_comp]
      rfl

/-- The newest source static name translates to the sole target symbol,
weakened below exactly the evidence block selected by its interval shape. -/
private theorem translateAvailableName
    {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (interval : DOTCapture.BinderOnly.Interval sort scope) :
    translateExpr (context.extendStatic interval)
        (DOTCapture.BinderOnly.StaticExpr.bound
          (.here : DOTCapture.BinderOnly.BVar
            (scope ▹ .static sort) (.static sort))) =
      ManySortedFC.Interval.name.rename
        (ManySortedFC.Rename.weakenMany
          (ManySortedFC.SymbolScope (sig context) [translateSort sort])
          (ManySortedFC.evidenceKinds (intervalRelations interval))) := by
  cases interval with
  | bounds lower upper =>
      cases lower <;> cases upper <;> cases sort <;> rfl

/-- Compile every shape-preserving source interval entailment into a checked
identity-on-symbols target theory morphism. -/
def compileEntails {scope : DOTCapture.BinderOnly.Sig}
    {context : DOTCapture.BinderOnly.Ctx scope}
    {sort : DOTCapture.BinderOnly.StaticSort}
    {available required : DOTCapture.BinderOnly.Interval sort scope}
    (entailment : DOTCapture.BinderOnly.Interval.Entails
      context available required) :
    EntailmentCompilation entailment :=
  match entailment with
  | .unbounded =>
      { morphism := ⟨.nil⟩
        typing := .nil }
  | @DOTCapture.BinderOnly.Interval.Entails.lower _ context sort
      availableLower requiredLower lowerEvidence =>
      let compiled := compileIncludesTotal lowerEvidence
      { morphism := ⟨.cons compiled.evidence .nil⟩
        typing := .cons (by
          have compiledTyping := compiled.typing
          rw [translateEndpointUnderInterval context
            (.bounds (.some availableLower) .none) requiredLower,
            translateAvailableName context
              (.bounds (.some availableLower) .none)] at compiledTyping
          simpa [translateInterval, intervalRelations,
            ManySortedFC.Interval.lowerBounded,
            ManySortedFC.Proposition.rename] using compiledTyping) .nil }
  | @DOTCapture.BinderOnly.Interval.Entails.upper _ context sort
      availableUpper requiredUpper upperEvidence =>
      let compiled := compileIncludesTotal upperEvidence
      { morphism := ⟨.cons compiled.evidence .nil⟩
        typing := .cons (by
          have compiledTyping := compiled.typing
          rw [translateAvailableName context
              (.bounds .none (.some availableUpper)),
            translateEndpointUnderInterval context
              (.bounds .none (.some availableUpper)) requiredUpper]
            at compiledTyping
          simpa [translateInterval, intervalRelations,
            ManySortedFC.Interval.upperBounded,
            ManySortedFC.Proposition.rename] using compiledTyping) .nil }
  | @DOTCapture.BinderOnly.Interval.Entails.between _ context sort
      availableLower availableUpper requiredLower requiredUpper
      lowerEvidence upperEvidence =>
      let compiledLower := compileIncludesTotal lowerEvidence
      let compiledUpper := compileIncludesTotal upperEvidence
      { morphism := ⟨.cons compiledLower.evidence
          (.cons compiledUpper.evidence .nil)⟩
        typing := .cons (by
          have compiledLowerTyping := compiledLower.typing
          rw [translateEndpointUnderInterval context
              (.bounds (.some availableLower) (.some availableUpper))
              requiredLower,
            translateAvailableName context
              (.bounds (.some availableLower) (.some availableUpper))]
            at compiledLowerTyping
          simpa [translateInterval, intervalRelations,
            ManySortedFC.Interval.between,
            ManySortedFC.Proposition.rename] using compiledLowerTyping)
          (.cons (by
          have compiledUpperTyping := compiledUpper.typing
          rw [translateAvailableName context
              (.bounds (.some availableLower) (.some availableUpper)),
            translateEndpointUnderInterval context
              (.bounds (.some availableLower) (.some availableUpper))
              requiredUpper] at compiledUpperTyping
          simpa [translateInterval, intervalRelations,
            ManySortedFC.Interval.between,
            ManySortedFC.Proposition.rename] using compiledUpperTyping)
            .nil) }

end DOTCaptureToManySortedFC.BinderOnly
