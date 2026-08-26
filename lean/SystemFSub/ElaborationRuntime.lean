import SystemFSub.ElaborationTerms
import SystemFSub.Metatheory
import SystemFCo.Operational

/-!
# An intrinsically scoped common runtime

A source type binder elaborates to a target type binder followed by a target
coercion binder. Erasing those binders outright would make a bare target
coercion abstraction cease to be a value. The common runtime therefore keeps
one abstraction/application phase per administrative binder: source type
abstractions/applications contribute two phases, while target type and
coercion abstractions/applications contribute one each.

Runtime scopes retain exactly the ordinary term-variable slots from a mixed
source or target scope. Thus the operational syntax is single-sorted but still
intrinsically scoped; type and coercion phases never create a second, parallel
term-variable index.
-/

namespace SystemFSub.Elaboration
namespace Runtime

abbrev Sig := List Unit

inductive BVar : Sig -> Type where
| here : BVar (() :: sig)
| there : BVar sig -> BVar (() :: sig)
deriving DecidableEq, Repr

inductive Term : Sig -> Type where
| var : BVar sig -> Term sig
| abs : Term (() :: sig) -> Term sig
| app : Term sig -> Term sig -> Term sig
| tabs : Term sig -> Term sig
| tapp : Term sig -> Term sig
deriving DecidableEq, Repr

structure Rename (source target : Sig) where
  var : BVar source -> BVar target

namespace Rename

def id : Rename sig sig where
  var := fun index => index

def lift (rename : Rename source target) :
    Rename (() :: source) (() :: target) where
  var := fun
    | .here => .here
    | .there index => .there (rename.var index)

def weaken : Rename sig (() :: sig) where
  var := BVar.there

end Rename

def Term.rename : Term source -> Rename source target -> Term target
| .var index, rename => .var (rename.var index)
| .abs body, rename => .abs (body.rename rename.lift)
| .app function argument, rename =>
    .app (function.rename rename) (argument.rename rename)
| .tabs body, rename => .tabs (body.rename rename)
| .tapp function, rename => .tapp (function.rename rename)

structure Subst (source target : Sig) where
  var : BVar source -> Term target

namespace Subst

def id : Subst sig sig where
  var := Term.var

def lift (substitution : Subst source target) :
    Subst (() :: source) (() :: target) where
  var := fun
    | .here => .var .here
    | .there index =>
        (substitution.var index).rename Rename.weaken

def openVar (argument : Term sig) : Subst (() :: sig) sig where
  var := fun
    | .here => argument
    | .there index => .var index

end Subst

def Term.subst : Term source -> Subst source target -> Term target
| .var index, substitution => substitution.var index
| .abs body, substitution => .abs (body.subst substitution.lift)
| .app function argument, substitution =>
    .app (function.subst substitution) (argument.subst substitution)
| .tabs body, substitution => .tabs (body.subst substitution)
| .tapp function, substitution => .tapp (function.subst substitution)

def Term.instantiate (body : Term (() :: sig)) (argument : Term sig) :
    Term sig :=
  body.subst (Subst.openVar argument)

inductive IsValue : Term sig -> Prop where
| abs : IsValue (.abs body)
| tabs : IsValue (.tabs body)

inductive Step : Term sig -> Term sig -> Prop where
| appFunction : Step function function' ->
    Step (.app function argument) (.app function' argument)
| appArgument : IsValue function -> Step argument argument' ->
    Step (.app function argument) (.app function argument')
| beta : IsValue argument ->
    Step (.app (.abs body) argument) (body.instantiate argument)
| tappFunction : Step function function' ->
    Step (.tapp function) (.tapp function')
| typeBeta : Step (.tapp (.tabs body)) body

inductive Steps : Term sig -> Term sig -> Prop where
| refl : Steps term term
| tail : Step first middle -> Steps middle last -> Steps first last

theorem Steps.single (step : Step first last) : Steps first last :=
  .tail step .refl

theorem Steps.trans (first : Steps term middle) (second : Steps middle last) :
    Steps term last := by
  induction first with
  | refl => exact second
  | tail step rest ih => exact .tail step (ih second)

theorem Steps.appFunction (steps : Steps function function') :
    Steps (.app function argument) (.app function' argument) := by
  induction steps with
  | refl => exact .refl
  | tail step rest ih => exact .tail (.appFunction step) ih

theorem Steps.appArgument (value : IsValue function)
    (steps : Steps argument argument') :
    Steps (.app function argument) (.app function argument') := by
  induction steps with
  | refl => exact .refl
  | tail step rest ih => exact .tail (.appArgument value step) ih

theorem Steps.tappFunction (steps : Steps function function') :
    Steps (.tapp function) (.tapp function') := by
  induction steps with
  | refl => exact .refl
  | tail step rest ih => exact .tail (.tappFunction step) ih

def IsNormal (term : Term sig) : Prop :=
  forall next, Not (Step term next)

def IsStuck (term : Term sig) : Prop :=
  IsNormal term /\ Not (IsValue term)

def GoesWrong (term : Term []) : Prop :=
  Exists fun result => Steps term result /\ IsStuck result

end Runtime

/-! ## Scope projection and syntax erasure -/

def targetRuntimeSig : SystemFCo.Sig -> Runtime.Sig
| [] => []
| .var :: tail => () :: targetRuntimeSig tail
| .tvar :: tail => targetRuntimeSig tail
| .cvar :: tail => targetRuntimeSig tail

def sourceRuntimeSig (sig : SystemFSub.Sig) : Runtime.Sig :=
  targetRuntimeSig (translateSig sig)

def eraseSourceVar : {sig : SystemFSub.Sig} ->
    SystemFSub.BVar sig .var -> Runtime.BVar (sourceRuntimeSig sig)
| _, .here => .here
| _, @SystemFSub.BVar.there tail .var .var index =>
    .there (eraseSourceVar (sig := tail) index)
| _, @SystemFSub.BVar.there tail .var .tvar index =>
    eraseSourceVar (sig := tail) index

def eraseTargetVar : {sig : SystemFCo.Sig} ->
    SystemFCo.BVar sig .var -> Runtime.BVar (targetRuntimeSig sig)
| _, .here => .here
| _, @SystemFCo.BVar.there tail .var .var index =>
    .there (eraseTargetVar (sig := tail) index)
| _, @SystemFCo.BVar.there tail .var .tvar index =>
    eraseTargetVar (sig := tail) index
| _, @SystemFCo.BVar.there tail .var .cvar index =>
    eraseTargetVar (sig := tail) index

def eraseSource : {sig : SystemFSub.Sig} -> (term : SystemFSub.Tm sig) ->
    Runtime.Term (sourceRuntimeSig sig)
| _, .var index => .var (eraseSourceVar index)
| _, .abs _ body => .abs (eraseSource body)
| _, .app function argument => .app (eraseSource function) (eraseSource argument)
| sig, .tabs _ body => .tabs (.tabs (eraseSource (sig := sig ,, .tvar) body))
| _, .tapp function _ => .tapp (.tapp (eraseSource function))

def eraseTarget : {sig : SystemFCo.Sig} -> (expression : SystemFCo.Exp sig) ->
    Runtime.Term (targetRuntimeSig sig)
| _, .var index => .var (eraseTargetVar index)
| _, .abs _ body => .abs (eraseTarget body)
| _, .app function argument => .app (eraseTarget function) (eraseTarget argument)
| sig, .tabs body => .tabs (eraseTarget (sig := sig ,, .tvar) body)
| _, .tapp function _ => .tapp (eraseTarget function)
| sig, .cabs _ _ body => .tabs (eraseTarget (sig := sig ,, .cvar) body)
| _, .capp function _ => .tapp (eraseTarget function)
| _, .cast expression _ => eraseTarget expression

end SystemFSub.Elaboration
