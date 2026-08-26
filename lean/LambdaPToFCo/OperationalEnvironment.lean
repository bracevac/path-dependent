import LambdaPToFCo.OperationalContexts
import SystemFCo.ReductionSubstitution

/-!
# Closing the compiler's mixed telescope at run time

The LambdaP CK machine interprets a variable by looking it up in an immutable
store.  An open System FCo variable is *not* a value, so an operational
correspondence cannot compare the open elaborations directly.  Instead, the
target image of a store is a simultaneous substitution that closes every
ordinary or exact-package interface allocated so far.

The definitions here are purely syntactic.  `Instantiation` describes the
one-slot/five-slot target data introduced by a source allocation;
`ClosingEnv.extend` composes that telescope substitution with the older
store image.  `StoreImage` leaves the eventual value-compilation invariant as
an explicit parameter rather than replacing it by a DOT-style realization
relation.
-/

namespace LambdaPToFCo
namespace OperationalEnvironment

open SystemFCo
open OperationalContexts

/-- Concrete target data represented by one compiled source binding.

An ordinary binding contributes one expression.  An exact binding contributes
the Church package plus the four pieces exposed by its unique unpacking:
hidden witness, lower evidence, upper evidence, and payload.  The package is
constructed from the latter pieces, so these data cannot silently disagree.
-/
inductive Instantiation : (plan : Interface.BinderPlan sig) -> Type where
| ordinary {valueType : Ty sig} (value : Exp sig) :
    Instantiation (.ordinary valueType)
| exact {lower upper : Ty sig} {payloadType : Ty (sig ,, .tvar)}
    (witness : Ty sig) (lowerEvidence upperEvidence : Co sig)
    (payload : Exp sig) :
    Instantiation (.exact lower upper payloadType)

namespace Instantiation

/-- The raw expression supplied to the compiled binder. -/
def argument : {plan : Interface.BinderPlan sig} ->
    Instantiation plan -> Exp sig
| _, .ordinary value => value
| _, @exact _ lower upper payloadType witness lowerEvidence upperEvidence
    payload =>
    Exp.packMember lower upper witness payloadType
      lowerEvidence upperEvidence payload

/-- Substitute all target slots introduced by this binder. -/
def substitution : {plan : Interface.BinderPlan sig} ->
    (actual : Instantiation plan) -> Subst plan.scope sig
| _, .ordinary value => Subst.openVar value
| _, @exact _ lower upper payloadType witness lowerEvidence upperEvidence
    payload =>
    OperationalMacros.CompiledBinder.exactSubst
      (Exp.packMember lower upper witness payloadType
        lowerEvidence upperEvidence payload)
      witness lowerEvidence upperEvidence payload

/-- Instantiate a body whose complete binder interface is in scope. -/
def instantiate {plan : Interface.BinderPlan sig}
    (actual : Instantiation plan) (body : Exp plan.scope) : Exp sig :=
  body.subst actual.substitution

/-- The operational precondition for eliminating a concrete binding.  For an
exact package only its payload must be a value: the Church package itself is
a type abstraction and therefore already a target value. -/
def Ready : {plan : Interface.BinderPlan sig} ->
    Instantiation plan -> Prop
| _, .ordinary value => Exp.IsValue value
| _, .exact _ _ _ payload => Exp.IsValue payload

theorem argument_isValue
    {plan : Interface.BinderPlan sig} {actual : Instantiation plan}
    (ready : Ready actual) : Exp.IsValue actual.argument := by
  cases actual with
  | ordinary => exact ready
  | exact => exact .tabs

/-- The complete administrative reduction for one allocated binding.  The
ordinary case is beta; the exact case is the Church package's seven-step
unpacking macro. -/
theorem close_steps
    {plan : Interface.BinderPlan sig} (actual : Instantiation plan)
    (ready : actual.Ready) (result : Ty sig) (body : Exp plan.scope) :
    Exp.Steps (plan.close actual.argument result body)
      (actual.instantiate body) := by
  cases actual with
  | ordinary value =>
      exact .tail
        (OperationalMacros.CompiledBinder.close_ordinary_step ready)
        .refl
  | @exact lower upper payloadType witness lowerEvidence upperEvidence
      payload =>
      exact OperationalMacros.CompiledBinder.close_exact_pack_steps
        ready

/-- Administrative binder reduction is stable underneath all outer compiled
CK frames. -/
theorem plug_close_steps
    (cont : Cont sig) {plan : Interface.BinderPlan sig}
    (actual : Instantiation plan) (ready : actual.Ready)
    (result : Ty sig) (body : Exp plan.scope) :
    Exp.Steps
      (cont.plug (plan.close actual.argument result body))
      (cont.plug (actual.instantiate body)) :=
  cont.plug_steps (actual.close_steps ready result body)

end Instantiation

/-- A target simultaneous substitution closing the compiler's current mixed
telescope into a fixed run-time signature. -/
structure ClosingEnv (source target : Sig) where
  substitution : Subst source target

namespace ClosingEnv

def identity : ClosingEnv sig sig :=
  ⟨Subst.id⟩

def closeExp (environment : ClosingEnv source target)
    (expression : Exp source) : Exp target :=
  expression.subst environment.substitution

def closeTy (environment : ClosingEnv source target)
    (ty : Ty source) : Ty target :=
  ty.subst environment.substitution

def closeCo (environment : ClosingEnv source target)
    (coercion : Co source) : Co target :=
  coercion.subst environment.substitution

/-- Extend a store image by the complete telescope of one compiled binding.
The new data are first interpreted in the old target scope and then closed by
the older environment. -/
def extend (environment : ClosingEnv sig target)
    {plan : Interface.BinderPlan sig} (actual : Instantiation plan) :
    ClosingEnv plan.scope target :=
  ⟨actual.substitution.comp environment.substitution⟩

/-- Closing after allocation is exactly instantiation followed by closing the
older store. -/
theorem closeExp_extend (environment : ClosingEnv sig target)
    {plan : Interface.BinderPlan sig} (actual : Instantiation plan)
    (body : Exp plan.scope) :
    (environment.extend actual).closeExp body =
      environment.closeExp (actual.instantiate body) := by
  exact (Exp.subst_comp body actual.substitution
    environment.substitution).symm

/-- The administrative elimination of one concrete binding remains valid
after the surrounding store environment closes every older target slot. -/
theorem close_binding_steps (environment : ClosingEnv sig target)
    {plan : Interface.BinderPlan sig} (actual : Instantiation plan)
    (ready : actual.Ready) (result : Ty sig) (body : Exp plan.scope) :
    Exp.Steps
      (environment.closeExp (plan.close actual.argument result body))
      (environment.closeExp (actual.instantiate body)) :=
  (actual.close_steps ready result body).subst environment.substitution

/-- Closed-store version of binder elimination underneath all suspended
compiled continuation frames. -/
theorem close_plug_binding_steps (environment : ClosingEnv sig target)
    (cont : Cont sig) {plan : Interface.BinderPlan sig}
    (actual : Instantiation plan) (ready : actual.Ready)
    (result : Ty sig) (body : Exp plan.scope) :
    Exp.Steps
      (environment.closeExp
        (cont.plug (plan.close actual.argument result body)))
      (environment.closeExp
        (cont.plug (actual.instantiate body))) :=
  (actual.plug_close_steps cont ready result body).subst
    environment.substitution

end ClosingEnv

/-! ## Structural source-store image

`ValueCompiler` is the remaining, explicitly named proof obligation: it must
connect one native source value to the concrete target instantiation selected
by its fragment typing derivation.  Keeping it as a parameter makes this
foundation usable now without smuggling in semantic store realization.
-/

abbrev ValueCompiler : Type :=
  {n : Nat} -> {sig : Sig} ->
  (value : LambdaPFC.Tm n) -> value.IsValue ->
  (plan : Interface.BinderPlan sig) -> Instantiation plan -> Prop

/-- A source store and its closing target substitution have the same
allocation spine.  Each source cell contributes one binder plan, even though
an exact plan contributes five target sorts. -/
inductive StoreImage :
    {n : Nat} -> LambdaPFC.Store n -> Sig -> Type where
| empty : StoreImage .empty []
| val
    {n : Nat} {sourceStore : LambdaPFC.Store n}
    {sig : Sig}
    {value : LambdaPFC.Tm n} {valueReady : value.IsValue}
    (older : StoreImage sourceStore sig)
    (plan : Interface.BinderPlan sig) (actual : Instantiation plan) :
    StoreImage (.val sourceStore value valueReady) plan.scope

namespace StoreImage

/-- Compute the closing substitution described by an allocation spine. -/
def environment
    {n : Nat}
    {sourceStore : LambdaPFC.Store n} {sig : Sig} :
    StoreImage sourceStore sig -> ClosingEnv sig []
| .empty => ClosingEnv.identity
| @val _ _ _ _ _ older plan actual =>
    (environment older).extend actual

/-- The separate invariant that connects every structural allocation cell to
the derivation-directed value compiler.  It is intentionally external to the
store spine, avoiding any semantic interpretation of source types. -/
def Valid (compileValue : ValueCompiler) :
    {n : Nat} -> {sourceStore : LambdaPFC.Store n} -> {sig : Sig} ->
    StoreImage sourceStore sig -> Prop
| _, _, _, .empty => True
| _, _, _, @val _ _ _ value valueReady older plan actual =>
    Valid compileValue older /\
      compileValue value valueReady plan actual

end StoreImage

end OperationalEnvironment
end LambdaPToFCo
