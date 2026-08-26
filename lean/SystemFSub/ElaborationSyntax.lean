import SystemFSub.Typing
import SystemFCo.Context

/-!
# The binder expansion used by the F<: elaboration

A source type-variable declaration `X <: B` becomes two independent target
declarations, in order:

1. a type variable `X`;
2. a coercion variable witnessing `X => B`.

Term declarations stay term declarations. This file contains only that
scope/type/context translation; derivation-directed term and coercion
elaboration is defined after the target typing judgment.
-/

namespace SystemFSub
namespace Elaboration

/-- Expand every source type binder to a target type binder followed by its
bound-evidence binder. -/
def translateSig : SystemFSub.Sig -> SystemFCo.Sig
| [] => []
| .var :: tail => SystemFCo.Sig.extend (translateSig tail) .var
| .tvar :: tail =>
    SystemFCo.Sig.extend
      (SystemFCo.Sig.extend (translateSig tail) .tvar) .cvar

/-- Translate an ordinary source variable into the expanded target scope. -/
def translateVar : {sig : SystemFSub.Sig} ->
    SystemFSub.BVar sig .var -> SystemFCo.BVar (translateSig sig) .var
| _, .here => .here
| _, @SystemFSub.BVar.there _ _ .var x =>
    .there (translateVar x)
| _, @SystemFSub.BVar.there _ _ .tvar x =>
    .there (.there (translateVar x))

/-- Translate a source type variable into the expanded target scope. -/
def translateTVar : {sig : SystemFSub.Sig} ->
    SystemFSub.BVar sig .tvar -> SystemFCo.BVar (translateSig sig) .tvar
| _, .here => .there .here
| _, @SystemFSub.BVar.there _ _ .var x =>
    .there (translateTVar x)
| _, @SystemFSub.BVar.there _ _ .tvar x =>
    .there (.there (translateTVar x))

/-- The coercion variable paired with a translated source type variable. -/
def translateBound : {sig : SystemFSub.Sig} ->
    SystemFSub.BVar sig .tvar -> SystemFCo.BVar (translateSig sig) .cvar
| _, .here => .here
| _, @SystemFSub.BVar.there _ _ .var x =>
    .there (translateBound x)
| _, @SystemFSub.BVar.there _ _ .tvar x =>
    .there (.there (translateBound x))

/-- Types translate homomorphically except for bounded universals. A bound is
made explicit as a coercion-qualified result underneath an ordinary type
abstraction. -/
def translateTy : {sig : SystemFSub.Sig} ->
    SystemFSub.Ty sig -> SystemFCo.Ty (translateSig sig)
| _, .top => .top
| _, .tvar x => .tvar (translateTVar x)
| _, .arrow parameter result =>
    .arrow (translateTy parameter) (translateTy result)
| _, .all bound body =>
    .poly (.qual (.tvar .here) ((translateTy bound).weaken .tvar)
      (translateTy body))

/-- Translate a source context into one mixed target telescope. -/
def translateCtx : {sig : SystemFSub.Sig} ->
    SystemFSub.Ctx sig -> SystemFCo.Ctx (translateSig sig)
| _, .empty => .empty
| _, .push context (.var T) =>
    (translateCtx context).bindVar (translateTy T)
| _, .push context (.tvar bound) =>
    ((translateCtx context).bindTVar).bindCVar
      (.tvar .here) ((translateTy bound).weaken .tvar)

end Elaboration
end SystemFSub
