import LambdaPToFCo.OperationalApplicationSpine
import LambdaPToFCo.OperationalPathCoherence
import LambdaPToFCo.TermTranslationNaturality

/-!
# Closed binder plans across one lexical extension

An older ordinary source type is renamed through a newly compiled binder.
Closing the extended target scope immediately substitutes that binder again,
so the older closed binder plan is unchanged.
-/

namespace LambdaPToFCo
namespace OperationalClosedPlanWeakening

open SystemFCo
open StaticTranslation
open OperationalBindingView
open OperationalEnvironment
open OperationalStoreEnvironment
open OperationalApplicationSpine

/-- Ordinary source representation is stable under source weakening. -/
def ordinaryShapeWeaken
    {sourceType : LambdaPFC.Ty n} (shape : OrdinaryShape sourceType) :
    OrdinaryShape sourceType.weaken := by
  cases shape <;> constructor

/-- A closed type is unaffected by renaming into an arbitrary mixed scope
and substituting that scope back to the empty signature. -/
theorem closed_type_rename_subst
    (ty : Ty []) (rename : Rename [] sig) (substitution : Subst sig []) :
    (ty.rename rename).subst substitution = ty := by
  rw [Ty.rename_asSubst, Ty.subst_comp]
  have cancel : rename.asSubst.comp substitution = Subst.id := by
    apply Subst.funext <;> intro index <;> cases index
  rw [cancel, Ty.subst_id]

/-- The plan's old-scope inclusion commutes with closing substitution for
types. -/
theorem type_rename_weaken_subst_scope
    (ty : Ty sig) (plan : Interface.BinderPlan sig)
    (substitution : Subst sig []) :
    (ty.rename plan.weaken).subst (plan.scopeSubst substitution) =
      (ty.subst substitution).rename (plan.subst substitution).weaken := by
  cases plan with
  | ordinary valueType =>
      exact (ty.weaken_subst_comm_base substitution).symm
  | exact lower upper payloadType =>
      simp only [Interface.BinderPlan.weaken,
        Interface.BinderPlan.scopeSubst, Interface.BinderPlan.subst_exact,
        ← Ty.rename_comp]
      change
        (((((ty.weaken .var).weaken .tvar).weaken .cvar).weaken .cvar).weaken
              .var).subst
            (((((substitution.lift .var).lift .tvar).lift .cvar).lift
                .cvar).lift .var) =
          (((((ty.subst substitution).weaken .var).weaken .tvar).weaken
              .cvar).weaken .cvar).weaken .var
      rw [← Ty.weaken_subst_comm_base, ← Ty.weaken_subst_comm_base,
        ← Ty.weaken_subst_comm_base, ← Ty.weaken_subst_comm_base,
        ← Ty.weaken_subst_comm_base]

/-- Closing an old type renamed through one later binder returns its former
closed type, independently of the new binding's behavior. -/
theorem close_old_type
    (closing : ClosingEnv sig []) (plan : Interface.BinderPlan sig)
    (view : EliminationView (plan.subst closing.substitution))
    (ty : Ty sig) :
    (extendClosing closing plan view).closeTy (ty.rename plan.weaken) =
      closing.closeTy ty := by
  rw [ClosingEnv.closeTy, extendClosing, ClosingEnv.closeTy,
    ← Ty.subst_comp, type_rename_weaken_subst_scope]
  exact closed_type_rename_subst (ty.subst closing.substitution)
    (plan.subst closing.substitution).weaken view.substitution

/-- The closed target binder plan of an older ordinary source type is
invariant under one newly compiled source binder. -/
theorem closedPlan_weaken
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {sourceType oldType : LambdaPFC.Ty n}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (oldWf : Fragment.Wf sourceContext oldType)
    (oldShape : OrdinaryShape oldType)
    (closing : ClosingEnv sig [])
    (view : EliminationView
      ((TermTranslation.compileBinder scope sourceWf).plan.subst
        closing.substitution)) :
    closedPlan (TermTranslation.compileBinder scope sourceWf).extended
        (extendClosing closing
          (TermTranslation.compileBinder scope sourceWf).plan view)
        (oldWf.weaken sourceType) =
      closedPlan scope closing oldWf := by
  let binder := TermTranslation.compileBinder scope sourceWf
  unfold closedPlan
  rw [OperationalValueEvidence.compileBinder_plan_ordinary binder.extended
      (oldWf.weaken sourceType) (ordinaryShapeWeaken oldShape),
    OperationalValueEvidence.compileBinder_plan_ordinary scope oldWf oldShape]
  simp only [Interface.BinderPlan.subst_ordinary]
  apply congrArg Interface.BinderPlan.ordinary
  rw [TermTranslation.compileBinder_naturality scope sourceWf oldWf]
  exact close_old_type closing binder.plan view (translateType scope oldWf)

end OperationalClosedPlanWeakening
end LambdaPToFCo
