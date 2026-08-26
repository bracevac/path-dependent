import LambdaPToFCo.Full.PairIntroductionTermCompiler
import LambdaPToFCo.Full.RecordIntroductionStaticRegression
import LambdaPToFCo.Full.GeneralPairIntroductionStaticRegression

/-!
# Certified direct-pair regressions

These checks place the two existing concrete Full pair introductions at the
normalized term boundary.  The value branch reuses the compiled
`RecordRegression.secondValue` producer.  The type branch reuses the direct
GeneralPair body producer and its demand-local singleton witness plan.  Thus
neither regression reconstructs, casts, or accepts a target package.
-/

namespace LambdaPToFCo.Full.PairIntroductionTermCompilationRegression

open LambdaPFC
open TranslationInterfaces

noncomputable section

namespace RecordValueMember

open RecordIntroductionStaticRegression

/-- The generic high constructor is definitionally indexed by the existing
Record value-member typing and producer. -/
noncomputable def compilation :
    NormalizedTermCompilation Source.typing context2Scope
      (.ordinary compiled) :=
  PairIntroductionTermCompiler.compileValuePair context2Scope (0 : Fin 2)
    (1 : Fin 2) LambdaPFC.RecordRegression.valueLabel

theorem suffix_eq : compilation.suffix = Tau.Sub.refl := by
  rfl

theorem root_origin_eq : compiled.origin =
    (TypingView.ofTyping Source.typing).rootOrigin :=
  compilation.root_origin_eq

end RecordValueMember

namespace GeneralPairTypeMember

open GeneralPairIntroductionStaticRegression

/-- The type-member high constructor reuses the existing demand-local witness
plan and exact GeneralPair direct body producer. -/
noncomputable def compilation :
    NormalizedTermCompilation exactBodySourceTyping bodyScope
      (.ordinary compiled) :=
  PairIntroductionTermCompiler.compileTypePairFromWitnessPlan bodyScope
    (0 : Fin 1) LambdaPFC.GeneralPairRegression.label witnessWf witnessPlan

theorem suffix_eq : compilation.suffix = Tau.Sub.refl := by
  rfl

theorem root_origin_eq : compiled.origin =
    (TypingView.ofTyping exactBodySourceTyping).rootOrigin :=
  compilation.root_origin_eq

end GeneralPairTypeMember

end

end LambdaPToFCo.Full.PairIntroductionTermCompilationRegression
