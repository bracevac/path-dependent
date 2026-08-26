import LambdaPToFCo.OperationalEnvironment

/-!
# Behavioral views of compiled bindings

`OperationalEnvironment.Instantiation.exact` is intentionally concrete: its
raw argument is a literal `packMember`.  That is not closed under package
covariance, because casting a package with `Co.member` produces a value whose
behavior is exposed only when the package is eliminated.

`BindingView` records exactly that behavior.  It consists of a raw argument,
the simultaneous substitution for the lexical slots exposed by its binder,
readiness of the raw argument, and a result/body-polymorphic reduction theorem
for eliminating it.  It does not interpret source types or assert a source
simulation.
-/

namespace LambdaPToFCo
namespace OperationalBindingView

open SystemFCo
open OperationalContexts
open OperationalEnvironment

/-- Behavioral interface of one compiled source binding. -/
structure BindingView (plan : Interface.BinderPlan sig) : Type where
  argument : Exp sig
  substitution : Subst plan.scope sig
  ready : Exp.IsValue argument
  eliminate : forall (result : Ty sig) (body : Exp plan.scope),
    Exp.Steps (plan.close argument result body)
      (body.subst substitution)

namespace BindingView

/-- The body produced by the view's lexical-slot substitution. -/
def instantiate {plan : Interface.BinderPlan sig}
    (view : BindingView plan) (body : Exp plan.scope) : Exp sig :=
  body.subst view.substitution

theorem close_steps {plan : Interface.BinderPlan sig}
    (view : BindingView plan) (result : Ty sig) (body : Exp plan.scope) :
    Exp.Steps (plan.close view.argument result body)
      (view.instantiate body) :=
  view.eliminate result body

/-- Every literal ordinary/exact instantiation embeds into the behavioral
interface. -/
def ofInstantiation {plan : Interface.BinderPlan sig}
    (actual : Instantiation plan) (ready : actual.Ready) :
    BindingView plan where
  argument := actual.argument
  substitution := actual.substitution
  ready := actual.argument_isValue ready
  eliminate := actual.close_steps ready

/-- Behavioral elimination remains valid under suspended compiled CK
frames. -/
theorem plug_close_steps {sig : Sig}
    {plan : Interface.BinderPlan sig}
    (view : BindingView plan) (cont : Cont sig)
    (result : Ty sig) (body : Exp plan.scope) :
    Exp.Steps
      (cont.plug (plan.close view.argument result body))
      (cont.plug (view.instantiate body)) :=
  cont.plug_steps (view.close_steps result body)

/-- Behavioral elimination remains valid after an older store environment
closes the current target scope. -/
theorem subst_close_steps {sig target : Sig}
    {plan : Interface.BinderPlan sig} (view : BindingView plan)
    (environment : ClosingEnv sig target)
    (result : Ty sig) (body : Exp plan.scope) :
    Exp.Steps
      (environment.closeExp (plan.close view.argument result body))
      (environment.closeExp (view.instantiate body)) :=
  (view.close_steps result body).subst environment.substitution

end BindingView

/-! ## Views with an administrative resumption -/

/-- A target evaluation context left behind by administrative coercion
reduction.  It transports computation one-for-one and disappears in finitely
many steps once its hole contains a value. -/
structure Resume (sig : Sig) : Type where
  plug : Exp sig -> Exp sig
  step : forall {first last : Exp sig}, Exp.Step first last ->
    Exp.Step (plug first) (plug last)
  discharge : forall {value : Exp sig}, Exp.IsValue value ->
    Exp.Steps (plug value) value

namespace Resume

def identity : Resume sig where
  plug := fun expression => expression
  step := fun reduction => reduction
  discharge := fun _ => .refl

/-- The administrative context introduced by the two covariant result
coercions in `Co.member`: one from the package arrow and one from the payload
handler arrow. -/
def doubleRefl (result : Ty sig) : Resume sig where
  plug := fun expression =>
    .cast (.cast expression (.refl result)) (.refl result)
  step := fun reduction =>
    .castExpression (.castExpression reduction)
  discharge := fun valueReady =>
    .tail (.castExpression (.castRefl valueReady))
      (.tail (.castRefl valueReady) .refl)

theorem steps (resume : Resume sig)
    (reductions : Exp.Steps first last) :
    Exp.Steps (resume.plug first) (resume.plug last) := by
  induction reductions with
  | refl => exact .refl
  | tail reduction rest ih => exact .tail (resume.step reduction) ih

/-- Compose two transparent administrative contexts.  `outer` remains
syntactically outside `inner`; discharging a value first removes the inner
context underneath `outer`, then removes `outer` itself. -/
def compose (outer inner : Resume sig) : Resume sig where
  plug := fun expression => outer.plug (inner.plug expression)
  step := fun reduction => outer.step (inner.step reduction)
  discharge := fun valueReady =>
    ((outer.steps (inner.discharge valueReady)).trans
      (outer.discharge valueReady))

@[simp] theorem compose_plug (outer inner : Resume sig)
    (expression : Exp sig) :
    (outer.compose inner).plug expression =
      outer.plug (inner.plug expression) := rfl

end Resume

/-- Behavioral binding view whose elimination may leave a transparent
administrative evaluation context around the instantiated body. -/
structure EliminationView (plan : Interface.BinderPlan sig) : Type where
  argument : Exp sig
  substitution : Subst plan.scope sig
  ready : Exp.IsValue argument
  resume : Ty sig -> Resume sig
  eliminate : forall (result : Ty sig) (body : Exp plan.scope),
    Exp.Steps (plan.close argument result body)
      ((resume result).plug (body.subst substitution))

namespace EliminationView

def instantiate {plan : Interface.BinderPlan sig}
    (view : EliminationView plan) (body : Exp plan.scope) : Exp sig :=
  body.subst view.substitution

/-- Transport a behavioral view across an explicit equality of binder plans.
This is useful when proof-relevant source well-formedness derivations select
definitionally different but propositionally equal compiler plans. -/
def castPlan {first second : Interface.BinderPlan sig}
    (equal : first = second) (view : EliminationView first) :
    EliminationView second :=
  equal ▸ view

@[simp] theorem castPlan_argument
    {first second : Interface.BinderPlan sig}
    (equal : first = second) (view : EliminationView first) :
    (castPlan equal view).argument = view.argument := by
  cases equal
  rfl

/-- A direct view is the special case with no administrative resumption. -/
def ofDirect {plan : Interface.BinderPlan sig}
    (view : BindingView plan) : EliminationView plan where
  argument := view.argument
  substitution := view.substitution
  ready := view.ready
  resume := fun _ => Resume.identity
  eliminate := view.eliminate

/-- Elimination followed by evaluation of the instantiated body and discharge
of the administrative context. -/
theorem finish_value {plan : Interface.BinderPlan sig}
    (view : EliminationView plan) (result : Ty sig)
    (body : Exp plan.scope) (value : Exp sig)
    (bodySteps : Exp.Steps (view.instantiate body) value)
    (valueReady : Exp.IsValue value) :
    Exp.Steps (plan.close view.argument result body) value :=
  (view.eliminate result body).trans
    (((view.resume result).steps bodySteps).trans
      ((view.resume result).discharge valueReady))

end EliminationView

end OperationalBindingView
end LambdaPToFCo
