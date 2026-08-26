import LambdaPToFCo.OperationalApplicationStore

/-!
# Source endpoint of the CK application case

The native CK `app` transition opens the abstraction body found in the store
with the argument location.  The compiler invariant instead retains the
abstraction's original lexical body and a valuation into the current store.
This module proves that those descriptions are the same source term.

Only three source-side facts are used:

* supported typed paths resolve to the static referents tracked by
  `StoreEnvironment`;
* native store lookup is deterministic;
* renaming a body under a lifted valuation and then opening it is the same as
  extending the original valuation by the returned location.

No target simulation or source preservation theorem is asserted here.
-/

namespace LambdaPToFCo
namespace OperationalApplicationSourceEndpoint

open OperationalApplicationStore
open OperationalCode
open OperationalStoreEnvironment

/-! ## Resolution of typed fragment paths -/

/-- Source subsumption does not change the static referent of a typed path,
so the existing path-resolution theorem extends to a full fragment typing
derivation for path syntax. -/
theorem resolveTypedPath
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : SystemFCo.Sig} {targetContext : SystemFCo.Ctx sig}
    {scope : StaticTranslation.Scope sourceContext targetContext}
    {closing : OperationalEnvironment.ClosingEnv sig []}
    (store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing) :
    {path : LambdaPFC.Path lexical} ->
    {sourceType : LambdaPFC.Ty lexical} ->
    (typing : Fragment.HasType sourceContext (.path path) sourceType) ->
    LambdaPFC.Path.Resolve (path.rename valuation) sourceStore
      (.loc (valuation (typedPathReferent typing)))
  | _, _, .path pathTyping => by
      simpa only [typedPathReferent_path] using store.resolvePath pathTyping
  | _, _, .sub inner _ => by
      simpa only [typedPathReferent_sub] using resolveTypedPath store inner

/-- Any CK resolution of a supported typed path reaches its statically
tracked store location. -/
theorem resolvedLocation_eq
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : SystemFCo.Sig} {targetContext : SystemFCo.Ctx sig}
    {scope : StaticTranslation.Scope sourceContext targetContext}
    {closing : OperationalEnvironment.ClosingEnv sig []}
    (store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    {path : LambdaPFC.Path lexical}
    {sourceType : LambdaPFC.Ty lexical}
    (typing : Fragment.HasType sourceContext (.path path) sourceType)
    {location : Fin current}
    (resolution : LambdaPFC.Path.Resolve (path.rename valuation) sourceStore
      (.loc location)) :
    location = valuation (typedPathReferent typing) := by
  have referentEq := resolution.deterministic (resolveTypedPath store typing)
  cases referentEq
  rfl

/-! ## Native abstraction-body identity -/

/-- If CK lookup and a compiled binding refer to the same native store cell,
the body named by the CK rule is the retained abstraction body under the
binding's native valuation. -/
theorem runtimeBody_eq
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {location : Fin current}
    {runtimeValue : LambdaPFC.Tm current}
    (binding : CompiledBinding runtimeValue)
    (function : CompiledBindingFunction binding)
    (bindingBinds : LambdaPFC.Store.Binds sourceStore location runtimeValue)
    {runtimeDomain : LambdaPFC.Ty current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (functionBinds : LambdaPFC.Store.Binds sourceStore location
      (.abs runtimeDomain runtimeBody)) :
    runtimeBody =
      function.sourceBody.rename binding.nativeValuation.ext := by
  have valueEq : runtimeValue = .abs runtimeDomain runtimeBody :=
    bindingBinds.unique functionBinds
  have absEq :
      LambdaPFC.Tm.abs
          (function.domain.rename binding.nativeValuation)
          (function.sourceBody.rename binding.nativeValuation.ext) =
        .abs runtimeDomain runtimeBody :=
    function.runtime_eq_abs.symm.trans valueEq
  cases absEq
  rfl

/-- Opening the CK body by the resolved argument location is exactly original
typed body code under the native valuation extended by that location. -/
theorem openRuntimeBody_eq
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {location : Fin current}
    {runtimeValue : LambdaPFC.Tm current}
    (binding : CompiledBinding runtimeValue)
    (function : CompiledBindingFunction binding)
    (bindingBinds : LambdaPFC.Store.Binds sourceStore location runtimeValue)
    {runtimeDomain : LambdaPFC.Ty current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (functionBinds : LambdaPFC.Store.Binds sourceStore location
      (.abs runtimeDomain runtimeBody))
    (argumentLocation : Fin current) :
    runtimeBody.open argumentLocation =
      function.sourceBody.rename
        (binding.nativeValuation.bind argumentLocation) := by
  rw [runtimeBody_eq binding function bindingBinds functionBinds]
  exact SourceValuation.rename_ext_openAt function.sourceBody
    binding.nativeValuation argumentLocation

/-! ## Lookup-level CK application endpoint -/

/-- Exact source endpoint required by the CK `app` simulation.

Both runtime path resolutions are reduced to the static referents of their
retained fragment typings.  The resulting opened CK body is the original
native abstraction body under the valuation extended by the argument's
static referent. -/
theorem lookup_app_open_eq
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : SystemFCo.Sig} {targetContext : SystemFCo.Ctx sig}
    {scope : StaticTranslation.Scope sourceContext targetContext}
    {closing : OperationalEnvironment.ClosingEnv sig []}
    (store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    {functionPath argumentPath : LambdaPFC.Path lexical}
    {domain codomain : LambdaPFC.Ty lexical}
    (functionTyping : Fragment.HasType sourceContext (.path functionPath)
      (.Fun domain codomain.weaken))
    (argumentTyping : Fragment.HasType sourceContext (.path argumentPath)
      domain)
    {functionLocation argumentLocation : Fin current}
    (functionResolution : LambdaPFC.Path.Resolve
      (functionPath.rename valuation) sourceStore (.loc functionLocation))
    (argumentResolution : LambdaPFC.Path.Resolve
      (argumentPath.rename valuation) sourceStore (.loc argumentLocation))
    {runtimeDomain : LambdaPFC.Ty current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (functionBinds : LambdaPFC.Store.Binds sourceStore functionLocation
      (.abs runtimeDomain runtimeBody))
    (function : CompiledBindingFunction
      (store.lookup (typedPathReferent functionTyping)).compiled) :
    runtimeBody.open argumentLocation =
      function.sourceBody.rename
        ((store.lookup
          (typedPathReferent functionTyping)).compiled.nativeValuation.bind
            (valuation (typedPathReferent argumentTyping))) := by
  have functionLocationEq :=
    resolvedLocation_eq store functionTyping functionResolution
  have argumentLocationEq :=
    resolvedLocation_eq store argumentTyping argumentResolution
  subst functionLocation
  subst argumentLocation
  exact openRuntimeBody_eq
    (store.lookup (typedPathReferent functionTyping)).compiled function
    (store.lookup (typedPathReferent functionTyping)).binds functionBinds
    (valuation (typedPathReferent argumentTyping))

end OperationalApplicationSourceEndpoint
end LambdaPToFCo
