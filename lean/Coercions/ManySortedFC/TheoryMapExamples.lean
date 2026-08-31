import Coercions.ManySortedFC.TheoryMapChecker
import Coercions.ManySortedFC.StaticExamples

/-!
# Cross-shape theory-map regressions

The examples cover the identity map, restriction of a mixed theory to its type
component, and rejection of an attempted target self-discharge from an
unconstrained source.
-/

namespace ManySortedFC.TheoryMapExamples

/-! ## A one-symbol identity map -/

def typeSymbol : StaticExpr .type (SymbolScope [] [.type]) :=
  .type (.tvar .here)

def exactTypeTheory : Theory [] [.type] [.equality .type] :=
  .cons (.equality typeSymbol (.type .one)) .nil

def exactTypeIdentity : TheoryMap exactTypeTheory exactTypeTheory :=
  TheoryMap.identity exactTypeTheory

theorem exact_type_identity_is_accepted :
    (TheoryMap.check Ctx.nil exactTypeIdentity).isSome = true := by
  native_decide

/-! ## Restrict a mixed theory to its type component -/

abbrev MixedOpenScope : Sig :=
  StaticScope [] [.type, .capture]
    [.equality .type, .equality .capture]

def mixedTypeOpened : StaticExpr .type MixedOpenScope :=
  StaticExamples.mixedTypeSymbol.rename
    (Rename.weakenMany (SymbolScope [] [.type, .capture])
      (evidenceKinds [.equality .type, .equality .capture]))

/-- Select the existing type name and its existing equality assumption.  The
capture name and capture assumption are simply omitted from the target view. -/
def mixedToType : TheoryMap StaticExamples.exactMixedTheory exactTypeTheory where
  symbols := .cons mixedTypeOpened .nil
  evidence := .cons (.var .here) .nil

theorem mixed_to_type_projection_is_accepted :
    (TheoryMap.check Ctx.nil mixedToType).isSome = true := by
  native_decide

theorem projection_changes_both_shapes :
    ([.type, .capture] : List StaticSort) ≠ [.type] ∧
      ([.equality .type, .equality .capture] : List Relation) ≠
        [.equality .type] := by
  decide

/-! ## The target cannot discharge itself -/

def unconstrainedType : Theory [] [.type] [] :=
  Interval.unconstrained .type

abbrev UnconstrainedOpenScope : Sig := StaticScope [] [.type] []

def unconstrainedTypeOpened : StaticExpr .type UnconstrainedOpenScope :=
  .type (.tvar .here)

/-- There is no source evidence variable to cite.  Reflexivity at the mapped
name is a well-kinded raw certificate, but it does not prove that name equal to
`One`, so structural checking rejects it. -/
def targetSelfDischargeAttempt :
    TheoryMap unconstrainedType exactTypeTheory where
  symbols := .cons unconstrainedTypeOpened .nil
  evidence := .cons (.equalityRefl unconstrainedTypeOpened) .nil

theorem target_self_discharge_is_rejected :
    TheoryMap.check Ctx.nil targetSelfDischargeAttempt = none := by
  native_decide

/-- More directly, opening the unconstrained source creates no type-equality
evidence coordinate at all. -/
theorem unconstrained_source_has_no_equality_assumption
    (index : BVar UnconstrainedOpenScope (.evidence (.equality .type))) : False :=
  nomatch index

end ManySortedFC.TheoryMapExamples
