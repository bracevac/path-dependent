import LambdaPToFCo.Full.PathPackageZipper

/-!
# Closing compiled path packages

Structural path projection may leave its result underneath one or more
Church eliminations.  A result can return to the root context exactly when
its focused plan is the root plan renamed by the zipper weakening.  This
module packages that small, proof-relevant closing condition and performs
the eliminations without exposing any hidden field in the root context.
-/

namespace LambdaPToFCo.Full.PathPackageZipper

open SystemFCoExt

namespace PathResult

/-- Close all retained package eliminations once the current plan is known to
be the root plan transported along the zipper weakening. -/
noncomputable def close
    {rootSig : Sig} {rootContext : Ctx rootSig}
    (result : PathResult rootContext)
    (rootPlan : ValuePlan rootSig)
    (plan_eq : result.plan = rootPlan.rename result.zipper.weakening) :
    CompiledPackage rootContext rootPlan := by
  have input_eq :
      result.plan.inputTy =
        rootPlan.inputTy.rename result.zipper.weakening := by
    rw [plan_eq]
    exact (ValuePlan.inputTy_rename rootPlan result.zipper.weakening).symm
  have bodyTyping :
      Exp.HasType result.currentContext result.package.expression
        (rootPlan.inputTy.rename result.zipper.weakening) := by
    exact input_eq ▸ result.package.typing
  let closed :=
    result.zipper.plug rootPlan.inputTy result.package.expression bodyTyping
  exact
    { expression := closed.expression
      typing := closed.typing }

end PathResult

end LambdaPToFCo.Full.PathPackageZipper
