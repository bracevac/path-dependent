import LambdaPToFCo.TermTranslationRegression
import LambdaPToFCo.TermTranslationSoundness

/-! End-to-end target typing for the closed term-compiler regression. -/

namespace LambdaPToFCo
namespace TermTranslationRegression

open SystemFCo
open StaticTranslation

/-- The actual target expression emitted for the closed source derivation. -/
noncomputable def compiledProgram : Exp ([] : Sig) :=
  TermTranslation.elaborate Scope.empty programTyping

/-- The compiled program is accepted by the standalone explicit-coercion
target type system. -/
noncomputable def compiledProgramTyping :
    Exp.HasType .empty compiledProgram
      (translateType Scope.empty programTyping.typeWf) :=
  TermTranslation.elaborate_hasType Scope.Coherent.empty programTyping

end TermTranslationRegression
end LambdaPToFCo
