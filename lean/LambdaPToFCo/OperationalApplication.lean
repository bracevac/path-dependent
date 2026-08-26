import LambdaPToFCo.OperationalBindingView

/-!
# Target-side application of compiled nondependent functions

This module isolates the target reduction used by the LambdaP CK `app`
simulation.  A compiled function starts as `BinderPlan.lambda`; source
function subtyping may surround it with reflexive, transitive, and structural
arrow casts.  Applying an arrow cast has two different operational effects:

* its contravariant coercion is pushed onto the argument and must produce the
  behavioral view expected by the inner binder;
* its covariant coercion remains around the result as a genuine target cast.

The second effect is deliberately not represented by
`OperationalBindingView.Resume`.  A `Resume` is transparent once its hole is
a value, whereas an arrow, package, or qualified result cast is itself a
value and must survive.  `ResultContext` is the weaker and correct abstraction
for those residual casts: it only promises closure under target reduction.

Everything below concerns target syntax and target reduction.  In particular,
`ArgumentView` is the explicit premise that an adapted argument has the
lexical-slot behavior required by a binder; no source store interpretation is
introduced here.
-/

namespace LambdaPToFCo
namespace OperationalApplication

open SystemFCo
open OperationalBindingView

/-! ## Reduction under the target contexts used by application -/

namespace Steps

/-- Evaluate the function position through a finite target reduction. -/
theorem appFunction (reductions : Exp.Steps function function') :
    Exp.Steps (.app function argument) (.app function' argument) := by
  induction reductions with
  | refl => exact .refl
  | tail reduction rest ih =>
      exact .tail (.appFunction reduction) ih

/-- Evaluate the argument position once the function is a target value. -/
theorem appArgument (functionReady : Exp.IsValue function)
    (reductions : Exp.Steps argument argument') :
    Exp.Steps (.app function argument) (.app function argument') := by
  induction reductions with
  | refl => exact .refl
  | tail reduction rest ih =>
      exact .tail (.appArgument functionReady reduction) ih

/-- Evaluate underneath one residual result cast. -/
theorem castExpression (reductions : Exp.Steps expression expression') :
    Exp.Steps (.cast expression coercion) (.cast expression' coercion) := by
  induction reductions with
  | refl => exact .refl
  | tail reduction rest ih =>
      exact .tail (.castExpression reduction) ih

end Steps

/-! ## Residual result contexts -/

/-- An evaluation context surrounding the instantiated function body.

Unlike `Resume`, this interface does not claim that the context disappears on
a value.  Structural codomain casts are observable target values, so reduction
closure is the strongest generally valid law. -/
structure ResultContext (sig : Sig) : Type where
  plug : Exp sig -> Exp sig
  step : forall {first last : Exp sig}, Exp.Step first last ->
    Exp.Step (plug first) (plug last)

namespace ResultContext

def identity : ResultContext sig where
  plug := fun expression => expression
  step := fun reduction => reduction

/-- Forget only the discharge law of a transparent administrative resume. -/
def ofResume (resume : Resume sig) : ResultContext sig where
  plug := resume.plug
  step := resume.step

/-- Retain a genuine target cast outside an existing result context. -/
def cast (context : ResultContext sig) (coercion : Co sig) :
    ResultContext sig where
  plug := fun expression => .cast (context.plug expression) coercion
  step := fun reduction => .castExpression (context.step reduction)

/-- Composition is useful when a caller already has a surrounding compiled
evaluation context.  `outer` remains syntactically outside `inner`. -/
def compose (outer inner : ResultContext sig) : ResultContext sig where
  plug := fun expression => outer.plug (inner.plug expression)
  step := fun reduction => outer.step (inner.step reduction)

theorem steps (context : ResultContext sig)
    (reductions : Exp.Steps first last) :
    Exp.Steps (context.plug first) (context.plug last) := by
  induction reductions with
  | refl => exact .refl
  | tail reduction rest ih => exact .tail (context.step reduction) ih

@[simp] theorem identity_plug (expression : Exp sig) :
    identity.plug expression = expression := rfl

@[simp] theorem ofResume_plug (resume : Resume sig)
    (expression : Exp sig) :
    (ofResume resume).plug expression = resume.plug expression := rfl

@[simp] theorem cast_plug (context : ResultContext sig)
    (coercion : Co sig) (expression : Exp sig) :
    (context.cast coercion).plug expression =
      .cast (context.plug expression) coercion := rfl

@[simp] theorem compose_plug (outer inner : ResultContext sig)
    (expression : Exp sig) :
    (outer.compose inner).plug expression =
      outer.plug (inner.plug expression) := rfl

end ResultContext

/-! ## Closed casts of ready arguments -/

/-- A cast has performed enough administration to expose a target value.

This is a behavioral witness rather than a claim that the coercion erases:
for a structural coercion, `result` is the cast-wrapped value itself. -/
structure CastNormalization {sig : Sig}
    (argument : Exp sig) (coercion : Co sig) : Type
    where
  result : Exp sig
  ready : Exp.IsValue result
  reductions : Exp.Steps (.cast argument coercion) result

namespace CastNormalization

def refl {sig : Sig} {argument : Exp sig}
    (argumentReady : Exp.IsValue argument) (ty : Ty sig) :
    CastNormalization (sig := sig) argument (Co.refl ty : Co sig) where
  result := argument
  ready := argumentReady
  reductions := .single (.castRefl argumentReady)

def top {sig : Sig} {argument : Exp sig}
    (argumentReady : Exp.IsValue argument) (source : Ty sig) :
    CastNormalization (sig := sig) argument (Co.top source : Co sig) where
  result := .cast argument (.top source)
  ready := .castTop argumentReady
  reductions := .refl

def arrow {sig : Sig} {argument : Exp sig}
    (argumentReady : Exp.IsValue argument)
    (domain codomain : Co sig) :
    CastNormalization (sig := sig) argument
      (Co.arrow domain codomain : Co sig) where
  result := .cast argument (.arrow domain codomain)
  ready := .castArrow argumentReady
  reductions := .refl

def poly {sig : Sig} {argument : Exp sig}
    (argumentReady : Exp.IsValue argument)
    (body : Co (sig ,, .tvar)) :
    CastNormalization (sig := sig) argument (Co.poly body : Co sig) where
  result := .cast argument (.poly body)
  ready := .castPoly argumentReady
  reductions := .refl

def qual {sig : Sig} {argument : Exp sig}
    (argumentReady : Exp.IsValue argument)
    (evidence result : Co (sig ,, .cvar)) :
    CastNormalization (sig := sig) argument
      (Co.qual evidence result : Co sig) where
  result := .cast argument (.qual evidence result)
  ready := .castQual argumentReady
  reductions := .refl

/-- Normalize a transitive cast by exposing its two object-language casts in
order.  Neither structural component is discarded. -/
def trans {sig : Sig} {argument : Exp sig}
    (argumentReady : Exp.IsValue argument)
    {first second : Co sig}
    (firstNormalization : CastNormalization (sig := sig) argument first)
    (secondNormalization :
      CastNormalization (sig := sig) firstNormalization.result second) :
    CastNormalization (sig := sig) argument
      (Co.trans first second : Co sig) where
  result := secondNormalization.result
  ready := secondNormalization.ready
  reductions :=
    (Exp.Steps.single (.castTrans argumentReady)).trans
      ((Steps.castExpression firstNormalization.reductions).trans
        secondNormalization.reductions)

/-- Every cast of a ready expression in the empty signature reaches a target
value.  A closed coercion has no `cvar` case; reflexive/transitive casts take
administrative steps and structural casts remain as value wrappers. -/
def closed {argument : Exp []} (argumentReady : Exp.IsValue argument) :
    (coercion : Co []) -> CastNormalization (sig := []) argument coercion
  | .cvar index => nomatch index
  | .refl ty => refl argumentReady ty
  | .trans first second =>
      let firstNormalization := closed argumentReady first
      trans argumentReady firstNormalization
        (closed firstNormalization.ready second)
  | .top source => top argumentReady source
  | .arrow domain codomain => arrow argumentReady domain codomain
  | .poly body => poly argumentReady body
  | .qual evidence result => qual argumentReady evidence result

end CastNormalization

/-! ## Canonical compiled functions -/

/-- A target value obtained from a compiled nondependent function.

The base is exactly the lambda emitted by a binder plan.  Each `arrow` node is
a structural function cast and therefore remains in the canonical value. -/
inductive FunctionValue {sig : Sig}
    (plan : Interface.BinderPlan sig) (result : Ty sig)
    (body : Exp plan.scope) : Type where
  | lambda
  | arrow (inner : FunctionValue plan result body)
      (domain codomain : Co sig)

namespace FunctionValue

def expression {sig : Sig} {plan : Interface.BinderPlan sig}
    {result : Ty sig} {body : Exp plan.scope} :
    FunctionValue plan result body -> Exp sig
  | .lambda => plan.lambda result body
  | .arrow inner domain codomain =>
      .cast inner.expression (.arrow domain codomain)

def ready {sig : Sig} {plan : Interface.BinderPlan sig}
    {result : Ty sig} {body : Exp plan.scope} :
    (view : FunctionValue plan result body) ->
    Exp.IsValue view.expression
  | .lambda => by
      cases plan <;> exact .abs
  | .arrow inner _ _ => .castArrow inner.ready

end FunctionValue

/-- The coercion forms admitted around a compiled function before it reaches
the canonical arrow-cast tower.  This is precisely the operational fragment
generated by reflexivity, transitivity, and function subtyping. -/
inductive FunctionCo (sig : Sig) : Type where
  | refl (ty : Ty sig)
  | trans (first second : FunctionCo sig)
  | arrow (domain codomain : Co sig)

namespace FunctionCo

def coercion : FunctionCo sig -> Co sig
  | .refl ty => .refl ty
  | .trans first second => .trans first.coercion second.coercion
  | .arrow domain codomain => .arrow domain codomain

end FunctionCo

/-- Normal form of supported administration around a compiled function. -/
structure FunctionNormalization {sig : Sig}
    (plan : Interface.BinderPlan sig) (result : Ty sig)
    (body : Exp plan.scope) (expression : Exp sig) : Type where
  value : FunctionValue plan result body
  reductions : Exp.Steps expression value.expression

namespace FunctionCo

/-- Apply supported coercion administration to an already canonical compiled
function value. -/
def normalize
    {plan : Interface.BinderPlan sig} {result : Ty sig}
    {body : Exp plan.scope}
    (coercionView : FunctionCo sig)
    (functionView : FunctionValue plan result body) :
    FunctionNormalization plan result body
      (.cast functionView.expression coercionView.coercion) :=
  match coercionView with
  | .refl _ =>
      { value := functionView
        reductions := Exp.Steps.single (.castRefl functionView.ready) }
  | .arrow domain codomain =>
      { value := .arrow functionView domain codomain
        reductions := .refl }
  | .trans first second =>
      let firstNormalization := first.normalize functionView
      let secondNormalization := second.normalize firstNormalization.value
      { value := secondNormalization.value
        reductions :=
          (Exp.Steps.single (.castTrans functionView.ready)).trans
            ((Steps.castExpression firstNormalization.reductions).trans
              secondNormalization.reductions) }

end FunctionCo

/-- Syntactic provenance of a compiled function before reflexive/transitive
administration has normalized.  Nested source subsumption becomes nested
`cast` constructors here. -/
inductive FunctionView {sig : Sig}
    (plan : Interface.BinderPlan sig) (result : Ty sig)
    (body : Exp plan.scope) : Type where
  | lambda
  | cast (inner : FunctionView plan result body)
      (coercion : FunctionCo sig)

namespace FunctionView

def expression {sig : Sig} {plan : Interface.BinderPlan sig}
    {result : Ty sig} {body : Exp plan.scope} :
    FunctionView plan result body -> Exp sig
  | .lambda => plan.lambda result body
  | .cast inner coercion => .cast inner.expression coercion.coercion

/-- Normalize all supported administration while retaining structural arrow
casts as part of the target value. -/
def normalize : (code : FunctionView plan result body) ->
    FunctionNormalization plan result body code.expression
  | .lambda =>
      { value := .lambda
        reductions := .refl }
  | .cast inner coercionView =>
      let innerNormalization := inner.normalize
      let outerNormalization :=
        coercionView.normalize innerNormalization.value
      { value := outerNormalization.value
        reductions :=
          (Steps.castExpression innerNormalization.reductions).trans
            outerNormalization.reductions }

end FunctionView

/-! ## Arguments accepted by a canonical function -/

/-- Layer-by-layer evidence that an outer ready argument reaches the
behavioral interface expected by the base binder.

At an arrow node, `adapt` normalizes the pushed contravariant cast only as far
as some ready expression; `inner` then describes the remaining arrow layers.
At the base, the imported `EliminationView` supplies the exact lexical-slot
substitution and any transparent package-administration `Resume`. -/
inductive ArgumentView
    {sig : Sig} {plan : Interface.BinderPlan sig} {result : Ty sig}
    {body : Exp plan.scope} :
    FunctionValue plan result body -> Exp sig -> Type where
  | lambda (view : EliminationView plan) :
      ArgumentView (.lambda : FunctionValue plan result body) view.argument
  | arrow {functionView : FunctionValue plan result body}
      {domain codomain : Co sig}
      {argument adapted : Exp sig}
      (argumentReady : Exp.IsValue argument)
      (adapt : Exp.Steps (.cast argument domain) adapted)
      (inner : ArgumentView functionView adapted) :
      ArgumentView (.arrow functionView domain codomain) argument

namespace ArgumentView

def ready {sig : Sig} {plan : Interface.BinderPlan sig}
    {result : Ty sig} {body : Exp plan.scope}
    {functionView : FunctionValue plan result body}
    {argument : Exp sig} : ArgumentView functionView argument ->
    Exp.IsValue argument
  | .lambda view => view.ready
  | .arrow argumentReady _ _ => argumentReady

def elimination {sig : Sig} {plan : Interface.BinderPlan sig}
    {result : Ty sig} {body : Exp plan.scope}
    {functionView : FunctionValue plan result body}
    {argument : Exp sig} : ArgumentView functionView argument ->
    EliminationView plan
  | .lambda view => view
  | .arrow _ _ inner => inner.elimination

/-- Use the total closed-cast normalization theorem for one arrow layer. -/
def arrowClosed
    {plan : Interface.BinderPlan []} {result : Ty []}
    {body : Exp plan.scope} {argument : Exp []}
    {domain codomain : Co []}
    {functionView : FunctionValue plan result body}
    (argumentReady : Exp.IsValue argument)
    (inner : ArgumentView functionView
      (CastNormalization.closed argumentReady domain).result) :
    ArgumentView (.arrow functionView domain codomain) argument :=
  .arrow argumentReady
    (CastNormalization.closed argumentReady domain).reductions inner

end ArgumentView

/-! ## The application macro -/

/-- Complete behavioral result of applying one canonical compiled function.

The endpoint exposes both parts needed by the source simulation: the precise
slot substitution selected by the base argument view, and the residual target
context (transparent `Resume` plus every surviving codomain cast) around the
compiled body. -/
structure ApplicationView
    {sig : Sig} {plan : Interface.BinderPlan sig} (body : Exp plan.scope)
    (function argument : Exp sig) : Type where
  elimination : EliminationView plan
  context : ResultContext sig
  reductions : Exp.Steps (.app function argument)
    (context.plug (body.subst elimination.substitution))

namespace FunctionValue

/-- Applying a canonical compiled function performs argument adaptation,
base binder elimination, and result-context construction in target order. -/
def application
    (functionView : FunctionValue plan result body)
    (argumentView : ArgumentView functionView argument) :
    ApplicationView body functionView.expression argument :=
  match functionView, argumentView with
  | .lambda, .lambda view =>
      { elimination := view
        context := .ofResume (view.resume result)
        reductions := by
          cases plan <;>
            simpa only [FunctionValue.expression,
              Interface.BinderPlan.lambda, Interface.BinderPlan.close,
              ResultContext.ofResume_plug] using
                view.eliminate result body }
  | .arrow innerFunction domain codomain,
      .arrow argumentReady adapt innerArgument =>
      let innerApplication := innerFunction.application innerArgument
      { elimination := innerApplication.elimination
        context := innerApplication.context.cast codomain
        reductions :=
          (Exp.Steps.single
            (.castArrowApp innerFunction.ready argumentReady)).trans
            ((Steps.castExpression
              (Steps.appArgument innerFunction.ready adapt)).trans
              (Steps.castExpression innerApplication.reductions)) }

/-- Direct specialization of the base application theorem.  Every imported
`BindingView` therefore applies to the exact lambda emitted by its binder plan;
the direct view selects the binder's precise slot substitution. -/
def applicationDirect
    {sig : Sig} {plan : Interface.BinderPlan sig}
    (view : BindingView plan) (result : Ty sig)
    (body : Exp plan.scope) :
    ApplicationView body (plan.lambda result body) view.argument :=
  (FunctionValue.lambda : FunctionValue plan result body).application
    (.lambda (.ofDirect view))

end FunctionValue

namespace FunctionView

/-- Application theorem for a not-yet-normalized compiled function.  Target
evaluation first normalizes its function position and then uses the canonical
application macro above. -/
def application
    (code : FunctionView plan result body)
    (argumentView : ArgumentView code.normalize.value argument) :
    ApplicationView body code.expression argument :=
  let canonical := code.normalize.value.application argumentView
  { elimination := canonical.elimination
    context := canonical.context
    reductions :=
      (Steps.appFunction code.normalize.reductions).trans
        canonical.reductions }

end FunctionView

end OperationalApplication
end LambdaPToFCo
