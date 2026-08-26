import LambdaPToFCo.Full.TranslationInterfaces

/-!
# Full let-package closing

A source `let` opens the compiled package of its bound term exactly once.
The body is compiled in that opened telescope.  It may leave the scope only
when its target plan is the chosen root result plan renamed through the same
telescope.  This is the target-side kernel; the higher compiler proves the
corresponding source weakening and model equality.
-/

namespace LambdaPToFCo.Full.LetCompilerCore

open SystemFCoExt
open TranslationInterfaces

/-- Eliminate the bound package and close a body package whose plan is the
root result plan transported into the opened binder context. -/
noncomputable def closeBody
    {sig : Sig} {base : Ctx sig}
    {boundPlan : ValuePlan sig}
    (bound : CompiledPackage base boundPlan)
    (resultPlan : ValuePlan sig)
    {bodyPlan : ValuePlan boundPlan.scope}
    (body : CompiledPackage (boundPlan.context base) bodyPlan)
    (plan_eq : bodyPlan = resultPlan.rename boundPlan.telescope.weaken) :
    CompiledPackage base resultPlan := by
  have input_eq :
      bodyPlan.inputTy =
        resultPlan.inputTy.rename boundPlan.telescope.weaken := by
    rw [plan_eq]
    exact
      (ValuePlan.inputTy_rename resultPlan boundPlan.telescope.weaken).symm
  have bodyTyping :
      Exp.HasType (boundPlan.context base) body.expression
        (resultPlan.inputTy.rename boundPlan.telescope.weaken) :=
    input_eq ▸ body.typing
  exact
    { expression := bound.consume resultPlan.inputTy body.expression
      typing := bound.consume_hasType resultPlan.inputTy body.expression
        bodyTyping }

end LambdaPToFCo.Full.LetCompilerCore
