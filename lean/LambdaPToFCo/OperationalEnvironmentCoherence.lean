import LambdaPToFCo.OperationalPathCoherenceGenerated
import LambdaPToFCo.OperationalFunctionEnvironmentCoherence
import LambdaPToFCo.OperationalStoreEnvironment

/-!
# Recursive coherence for compiled store environments

`StorePathCoherence` describes the lexical environment currently in use, but
every physical binding also retains the independent environment in which its
native code originated.  Function application re-enters precisely that
environment, so coherence of only the outer lexical view is insufficient.

`EnvironmentCoherence` mirrors the five `StoreEnvironment` constructors.  It
retains current path coherence and recursively retains the same invariant for
every native environment inserted by allocation or existing-location
binding.  Lookup can therefore recover a coherent native origin without
changing `StoreEnvironment` or `LocatedBinding`.
-/

namespace LambdaPToFCo
namespace OperationalEnvironmentCoherence

open SystemFCo
open StaticTranslation
open OperationalCode
open OperationalBindingView
open OperationalEnvironment
open OperationalStoreEnvironment
open OperationalAdmissibility
open OperationalApplicationSpine
open OperationalPathCoherence
open OperationalPathCoherenceGenerated
open OperationalFunctionEnvironmentCoherence

/-- Path coherence closed recursively under every native environment retained
inside a compiled store environment. -/
inductive EnvironmentCoherence :
    {lexical : Nat} ->
    {sourceContext : LambdaPFC.Ctx lexical} ->
    {current : Nat} ->
    {sourceStore : LambdaPFC.Store current} ->
    {valuation : SourceValuation lexical current} ->
    {sig : Sig} ->
    {targetContext : Ctx sig} ->
    {scope : Scope sourceContext targetContext} ->
    {closing : ClosingEnv sig []} ->
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing) -> Type where
  | empty
      (currentFunctionCoherent :
        FunctionEnvironmentCoherence StoreEnvironment.empty)
      (currentCoherent : StorePathCoherence StoreEnvironment.empty) :
      EnvironmentCoherence StoreEnvironment.empty
  | nativeWeaken
      {lexical current : Nat}
      {sourceContext : LambdaPFC.Ctx lexical}
      {sourceStore : LambdaPFC.Store current}
      {valuation : SourceValuation lexical current}
      {sig : Sig} {targetContext : Ctx sig}
      {scope : Scope sourceContext targetContext}
      {closing : ClosingEnv sig []}
      {older : StoreEnvironment sourceContext sourceStore valuation
        targetContext scope closing}
      (olderCoherent : EnvironmentCoherence older)
      (runtimeValue : LambdaPFC.Tm current)
      (runtimeReady : runtimeValue.IsValue)
      (currentFunctionCoherent : FunctionEnvironmentCoherence
        (StoreEnvironment.nativeWeaken older runtimeValue runtimeReady))
      (currentCoherent : StorePathCoherence
        (StoreEnvironment.nativeWeaken older runtimeValue runtimeReady)) :
      EnvironmentCoherence
        (StoreEnvironment.nativeWeaken older runtimeValue runtimeReady)
  | extend
      {lexical current : Nat}
      {sourceContext : LambdaPFC.Ctx lexical}
      {sourceStore : LambdaPFC.Store current}
      {valuation : SourceValuation lexical current}
      {sig : Sig} {targetContext : Ctx sig}
      {scope : Scope sourceContext targetContext}
      {olderClosing : ClosingEnv sig []}
      {older : StoreEnvironment sourceContext sourceStore valuation
        targetContext scope olderClosing}
      {sourceTerm : LambdaPFC.Tm lexical}
      {sourceType : LambdaPFC.Ty lexical}
      {typing : Fragment.HasType sourceContext sourceTerm sourceType}
      {native : TypedCode}
      {nativeValuation : SourceValuation native.arity current}
      {nativeAdmissible : OperationallyAdmissible native.typing}
      {nativeEvidence : ApplicationValueEvidence native.typing}
      {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
      {nativeScope : Scope native.context nativeTargetContext}
      {nativeClosing : ClosingEnv nativeSig []}
      {nativeEnvironment : StoreEnvironment native.context sourceStore
        nativeValuation nativeTargetContext nativeScope nativeClosing}
      {nativeReady : nativeEvidence.ClosedReady nativeScope nativeClosing}
      (runtimeValue : LambdaPFC.Tm current)
      (runtimeReady : runtimeValue.IsValue)
      {runtime_eq : runtimeValue = native.term.rename nativeValuation}
      {memberCell : MemberCell sourceType
        (.val sourceStore runtimeValue runtimeReady) valuation.weaken 0}
      {functionCell : FunctionCell sourceType
        (.val sourceStore runtimeValue runtimeReady) valuation.weaken 0}
      {behavior : EliminationView
        ((TermTranslation.compileBinder scope typing.typeWf).plan.subst
          olderClosing.substitution)}
      {normalizes : Exp.Steps
        (olderClosing.closeExp (TermTranslation.elaborate scope typing))
        behavior.argument}
      (olderCoherent : EnvironmentCoherence older)
      (nativeCoherent : EnvironmentCoherence nativeEnvironment)
      (currentFunctionCoherent : FunctionEnvironmentCoherence
        (StoreEnvironment.extend older typing native nativeValuation
          nativeAdmissible nativeEvidence nativeEnvironment nativeReady
          runtimeReady runtime_eq memberCell functionCell behavior
          normalizes))
      (currentCoherent : StorePathCoherence
        (StoreEnvironment.extend older typing native nativeValuation
          nativeAdmissible nativeEvidence nativeEnvironment nativeReady
          runtimeReady runtime_eq memberCell functionCell behavior
          normalizes)) :
      EnvironmentCoherence
        (StoreEnvironment.extend older typing native nativeValuation
          nativeAdmissible nativeEvidence nativeEnvironment nativeReady
          runtimeReady runtime_eq memberCell functionCell behavior
          normalizes)
  | alias
      {lexical current : Nat}
      {sourceContext : LambdaPFC.Ctx lexical}
      {sourceStore : LambdaPFC.Store current}
      {valuation : SourceValuation lexical current}
      {sig : Sig} {targetContext : Ctx sig}
      {scope : Scope sourceContext targetContext}
      {olderClosing : ClosingEnv sig []}
      {older : StoreEnvironment sourceContext sourceStore valuation
        targetContext scope olderClosing}
      {path : LambdaPFC.Path lexical}
      {sourceType : LambdaPFC.Ty lexical}
      (typing : Fragment.HasType sourceContext (.path path) sourceType)
      {memberCell : MemberCell sourceType sourceStore valuation
        (valuation (typedPathReferent typing))}
      {functionCell : FunctionCell sourceType sourceStore valuation
        (valuation (typedPathReferent typing))}
      {behavior : EliminationView
        ((TermTranslation.compileBinder scope typing.typeWf).plan.subst
          olderClosing.substitution)}
      {normalizes : Exp.Steps
        (olderClosing.closeExp (TermTranslation.elaborate scope typing))
        behavior.argument}
      (olderCoherent : EnvironmentCoherence older)
      (currentFunctionCoherent : FunctionEnvironmentCoherence
        (StoreEnvironment.alias older typing memberCell functionCell behavior
          normalizes))
      (currentCoherent : StorePathCoherence
        (StoreEnvironment.alias older typing memberCell functionCell behavior
          normalizes)) :
      EnvironmentCoherence
        (StoreEnvironment.alias older typing memberCell functionCell behavior
          normalizes)
  | bindLocation
      {lexical current : Nat}
      {sourceContext : LambdaPFC.Ctx lexical}
      {sourceStore : LambdaPFC.Store current}
      {valuation : SourceValuation lexical current}
      {sig : Sig} {targetContext : Ctx sig}
      {scope : Scope sourceContext targetContext}
      {olderClosing : ClosingEnv sig []}
      {older : StoreEnvironment sourceContext sourceStore valuation
        targetContext scope olderClosing}
      {sourceType : LambdaPFC.Ty lexical}
      {sourceWf : Fragment.Wf sourceContext sourceType}
      {location : Fin current}
      {runtimeValue : LambdaPFC.Tm current}
      {binds : LambdaPFC.Store.Binds sourceStore location runtimeValue}
      {compiled : CompiledBinding runtimeValue}
      {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
      {nativeScope : Scope compiled.native.context nativeTargetContext}
      {nativeClosing : ClosingEnv nativeSig []}
      {nativeEnvironment : StoreEnvironment compiled.native.context sourceStore
        compiled.nativeValuation nativeTargetContext nativeScope nativeClosing}
      {memberCell : MemberCell sourceType sourceStore valuation location}
      {functionCell : FunctionCell sourceType sourceStore valuation location}
      {behavior : EliminationView
        ((TermTranslation.compileBinder scope sourceWf).plan.subst
          olderClosing.substitution)}
      (olderCoherent : EnvironmentCoherence older)
      (nativeCoherent : EnvironmentCoherence nativeEnvironment)
      (currentFunctionCoherent : FunctionEnvironmentCoherence
        (StoreEnvironment.bindLocation older sourceWf location binds compiled
          nativeEnvironment memberCell functionCell behavior))
      (currentCoherent : StorePathCoherence
        (StoreEnvironment.bindLocation older sourceWf location binds compiled
          nativeEnvironment memberCell functionCell behavior)) :
      EnvironmentCoherence
        (StoreEnvironment.bindLocation older sourceWf location binds compiled
          nativeEnvironment memberCell functionCell behavior)

namespace EnvironmentCoherence

/-- The current lexical path invariant retained by recursive environment
coherence. -/
noncomputable def pathCoherence
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    {environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing}
    (coherent : EnvironmentCoherence environment) :
    StorePathCoherence environment := by
  cases coherent with
  | empty _ currentCoherent => exact currentCoherent
  | nativeWeaken _ _ _ _ currentCoherent => exact currentCoherent
  | extend _ _ _ _ _ currentCoherent => exact currentCoherent
  | alias _ _ _ currentCoherent => exact currentCoherent
  | bindLocation _ _ _ currentCoherent => exact currentCoherent

/-- The current lexical function invariant retained by recursive environment
coherence. -/
noncomputable def functionCoherence
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    {environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing}
    (coherent : EnvironmentCoherence environment) :
    FunctionEnvironmentCoherence environment := by
  cases coherent with
  | empty currentFunctionCoherent _ => exact currentFunctionCoherent
  | nativeWeaken _ _ _ currentFunctionCoherent _ =>
      exact currentFunctionCoherent
  | extend _ _ _ _ currentFunctionCoherent _ =>
      exact currentFunctionCoherent
  | alias _ _ currentFunctionCoherent _ => exact currentFunctionCoherent
  | bindLocation _ _ currentFunctionCoherent _ =>
      exact currentFunctionCoherent

/-- Canonical recursive coherence of the empty environment. -/
def initial : EnvironmentCoherence StoreEnvironment.initial := by
  change EnvironmentCoherence StoreEnvironment.empty
  exact .empty FunctionEnvironmentCoherence.initial StorePathCoherence.empty

/-- Recursive coherence survives a native allocation hidden from the lexical
environment. -/
noncomputable def weaken
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    {environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing}
    (coherent : EnvironmentCoherence environment)
    (runtimeValue : LambdaPFC.Tm current)
    (runtimeReady : runtimeValue.IsValue) :
    EnvironmentCoherence
      (StoreEnvironment.nativeWeaken environment runtimeValue runtimeReady) :=
  .nativeWeaken coherent runtimeValue runtimeReady
    (coherent.functionCoherence.nativeWeaken runtimeValue runtimeReady)
    (StorePathCoherence.nativeWeaken coherent.pathCoherence runtimeValue
      runtimeReady)

/-- Build recursive coherence for native allocation and lexical extension
from the generated local slot laws. -/
noncomputable def extendGenerated
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {olderClosing : ClosingEnv sig []}
    {older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope olderClosing}
    (olderCoherent : EnvironmentCoherence older)
    {sourceTerm : LambdaPFC.Tm lexical}
    {sourceType : LambdaPFC.Ty lexical}
    (typing : Fragment.HasType sourceContext sourceTerm sourceType)
    (native : TypedCode)
    (nativeValuation : SourceValuation native.arity current)
    (nativeAdmissible : OperationallyAdmissible native.typing)
    (nativeEvidence : ApplicationValueEvidence native.typing)
    {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
    {nativeScope : Scope native.context nativeTargetContext}
    {nativeClosing : ClosingEnv nativeSig []}
    (nativeEnvironment : StoreEnvironment native.context sourceStore
      nativeValuation nativeTargetContext nativeScope nativeClosing)
    (nativeCoherent : EnvironmentCoherence nativeEnvironment)
    (nativeReady : nativeEvidence.ClosedReady nativeScope nativeClosing)
    {runtimeValue : LambdaPFC.Tm current}
    (runtimeReady : runtimeValue.IsValue)
    (runtime_eq : runtimeValue = native.term.rename nativeValuation)
    (memberCell : MemberCell sourceType
      (.val sourceStore runtimeValue runtimeReady) valuation.weaken 0)
    (functionCell : FunctionCell sourceType
      (.val sourceStore runtimeValue runtimeReady) valuation.weaken 0)
    (behavior : EliminationView
      ((TermTranslation.compileBinder scope typing.typeWf).plan.subst
        olderClosing.substitution))
    (normalizes : Exp.Steps
      (olderClosing.closeExp (TermTranslation.elaborate scope typing))
      behavior.argument)
    (laws : BehaviorPathCoherence scope typing.typeWf olderClosing behavior
      (storeArguments older))
    (newest :
      {domain codomain : LambdaPFC.Ty lexical} ->
      sourceType = .Fun domain codomain.weaken ->
      Nonempty
        (FunctionBindingWitness scope olderClosing behavior domain sourceStore
          runtimeValue nativeEnvironment)) :
    EnvironmentCoherence
      (StoreEnvironment.extend older typing native nativeValuation
        nativeAdmissible nativeEvidence nativeEnvironment nativeReady
        runtimeReady runtime_eq memberCell functionCell behavior
        normalizes) :=
  .extend runtimeValue runtimeReady olderCoherent nativeCoherent
    (olderCoherent.functionCoherence.extend typing native nativeValuation
      nativeAdmissible nativeEvidence nativeEnvironment nativeReady
      runtimeReady runtime_eq memberCell functionCell behavior normalizes
      newest)
    (storePathCoherence_extend olderCoherent.pathCoherence typing native
      nativeValuation nativeAdmissible nativeEvidence nativeEnvironment
      nativeReady runtimeReady runtime_eq memberCell functionCell behavior
      normalizes laws)

/-- Build recursive coherence for a lexical alias from its generated local
slot laws.  The alias introduces no new native environment. -/
noncomputable def aliasGenerated
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {olderClosing : ClosingEnv sig []}
    {older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope olderClosing}
    (olderCoherent : EnvironmentCoherence older)
    {path : LambdaPFC.Path lexical}
    {sourceType : LambdaPFC.Ty lexical}
    (typing : Fragment.HasType sourceContext (.path path) sourceType)
    (shape : NonCanonicalResultShape sourceType)
    (memberCell : MemberCell sourceType sourceStore valuation
      (valuation (typedPathReferent typing)))
    (functionCell : FunctionCell sourceType sourceStore valuation
      (valuation (typedPathReferent typing)))
    (behavior : EliminationView
      ((TermTranslation.compileBinder scope typing.typeWf).plan.subst
        olderClosing.substitution))
    (normalizes : Exp.Steps
      (olderClosing.closeExp (TermTranslation.elaborate scope typing))
      behavior.argument)
    (laws : BehaviorPathCoherence scope typing.typeWf olderClosing behavior
      (storeArguments older)) :
    EnvironmentCoherence
      (StoreEnvironment.alias older typing memberCell functionCell behavior
        normalizes) :=
  .alias typing olderCoherent
    (olderCoherent.functionCoherence.aliasNonCanonical typing shape memberCell
      functionCell behavior normalizes)
    (storePathCoherence_alias olderCoherent.pathCoherence typing memberCell
      functionCell behavior normalizes laws)

/-- Build recursive coherence when a lexical binder aliases an explicitly
chosen physical location. -/
noncomputable def bindLocationGenerated
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {olderClosing : ClosingEnv sig []}
    {older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope olderClosing}
    (olderCoherent : EnvironmentCoherence older)
    {sourceType : LambdaPFC.Ty lexical}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (shape : NonCanonicalResultShape sourceType)
    (location : Fin current)
    {runtimeValue : LambdaPFC.Tm current}
    (binds : LambdaPFC.Store.Binds sourceStore location runtimeValue)
    (compiled : CompiledBinding runtimeValue)
    {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
    {nativeScope : Scope compiled.native.context nativeTargetContext}
    {nativeClosing : ClosingEnv nativeSig []}
    (nativeEnvironment : StoreEnvironment compiled.native.context sourceStore
      compiled.nativeValuation nativeTargetContext nativeScope nativeClosing)
    (nativeCoherent : EnvironmentCoherence nativeEnvironment)
    (memberCell : MemberCell sourceType sourceStore valuation location)
    (functionCell : FunctionCell sourceType sourceStore valuation location)
    (behavior : EliminationView
      ((TermTranslation.compileBinder scope sourceWf).plan.subst
        olderClosing.substitution))
    (laws : BehaviorPathCoherence scope sourceWf olderClosing behavior
      (storeArguments older)) :
    EnvironmentCoherence
      (StoreEnvironment.bindLocation older sourceWf location binds compiled
        nativeEnvironment memberCell functionCell behavior) :=
  .bindLocation olderCoherent nativeCoherent
    (olderCoherent.functionCoherence.bindLocationNonCanonical sourceWf shape
      location binds compiled nativeEnvironment memberCell functionCell
      behavior)
    (storePathCoherence_bindLocation olderCoherent.pathCoherence sourceWf
      location binds compiled nativeEnvironment memberCell functionCell
      behavior laws)

/-- Lookup recovers recursive coherence for the native environment retained
by the selected physical binding.  Aliases delegate to their static
referent; allocations weaken both newest and older native origins. -/
noncomputable def lookupNative
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    {environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing}
    (coherent : EnvironmentCoherence environment) (index : Fin lexical) :
    EnvironmentCoherence (environment.lookup index).nativeEnvironment := by
  induction coherent with
  | empty _ _ => exact Fin.elim0 index
  | nativeWeaken _ runtimeValue runtimeReady _ _ olderIH =>
      exact (olderIH index).weaken runtimeValue runtimeReady
  | extend runtimeValue runtimeReady _ nativeCoherent _ _ olderIH _ =>
      refine Fin.cases ?_ (fun olderIndex => ?_) index
      · exact nativeCoherent.weaken runtimeValue runtimeReady
      · exact (olderIH olderIndex).weaken runtimeValue runtimeReady
  | alias typing _ _ _ olderIH =>
      refine Fin.cases ?_ (fun olderIndex => ?_) index
      · exact olderIH (typedPathReferent typing)
      · exact olderIH olderIndex
  | bindLocation _ nativeCoherent _ _ olderIH _ =>
      refine Fin.cases ?_ (fun olderIndex => ?_) index
      · exact nativeCoherent
      · exact olderIH olderIndex

/-- Path coherence of the native environment returned by lookup. -/
noncomputable def lookupNativePathCoherence
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    {environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing}
    (coherent : EnvironmentCoherence environment) (index : Fin lexical) :
    StorePathCoherence (environment.lookup index).nativeEnvironment :=
  (coherent.lookupNative index).pathCoherence

end EnvironmentCoherence

end OperationalEnvironmentCoherence
end LambdaPToFCo
