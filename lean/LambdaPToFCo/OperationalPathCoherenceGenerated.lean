import LambdaPToFCo.OperationalPathCoherence
import LambdaPToFCo.OperationalAdmissibility

/-!
# Path coherence of generated closed binding views

`EliminationView` deliberately permits arbitrary substitutions, so the path
laws in `OperationalPathCoherence` cannot hold for every view.  This module
proves those laws for the concrete closed views emitted by the value compiler
and the ordinary argument adapter.  It also supplies store-constructor
wrappers which consume the laws explicitly, without strengthening or
mutating `StoreEnvironment`.
-/

namespace LambdaPToFCo
namespace OperationalPathCoherenceGenerated

open SystemFCo
open StaticTranslation
open OperationalCode
open OperationalBindingView
open OperationalEnvironment
open OperationalApplicationTranslation
open OperationalStoreEnvironment
open OperationalValueEvidence
open OperationalApplicationSpine
open OperationalAdmissibility
open OperationalPathCoherence

/-! ## Concrete target views -/

/-- Every direct closed instantiation maps its raw binder projection back to
the argument advertised by the resulting view. -/
theorem rawSlot_ofInstantiation
    {plan : Interface.BinderPlan []}
    (actual : Instantiation plan) (ready : actual.Ready) :
    RawSlot
      (EliminationView.ofDirect
        (BindingView.ofInstantiation actual ready)) := by
  cases actual with
  | ordinary => rfl
  | @exact lower upper payloadType witness lowerEvidence upperEvidence
      payload =>
      let package := Exp.packMember lower upper witness payloadType
        lowerEvidence upperEvidence payload
      simp only [RawSlot, binderRawExpression,
        EliminationView.ofDirect, BindingView.ofInstantiation,
        Instantiation.argument, Instantiation.substitution,
        OperationalMacros.CompiledBinder.exactSubst, Exp.subst,
        Subst.comp, Subst.lift_var_there, Subst.openVar]
      change
        (((((((package.weaken .tvar).weaken .cvar).weaken .cvar).weaken
                  .var).subst
              (((Subst.openTVar witness).lift .cvar).lift .cvar |>.lift
                .var)).subst
            ((Subst.openCVar lowerEvidence).lift .cvar |>.lift .var)).subst
          ((Subst.openCVar upperEvidence).lift .var)).subst
        (Subst.openVar payload) = package
      simp only [OperationalMacros.CompiledBinder.exp_weaken_subst_lift,
        OperationalMacros.CompiledBinder.exp_weaken_openVar,
        OperationalMacros.CompiledBinder.exp_weaken_openTVar,
        OperationalMacros.CompiledBinder.exp_weaken_openCVar]

/-- A direct exact instantiation exposes its literal payload in the newest
term slot. -/
theorem memberPayload_ofInstantiation
    {lower upper : Ty []} {payloadType : Ty ([.tvar])}
    (witness : Ty []) (lowerEvidence upperEvidence : Co [])
    (payload : Exp []) (ready : Exp.IsValue payload) :
    MemberPayload
      (EliminationView.ofDirect
        (BindingView.ofInstantiation
          (Instantiation.exact
            (lower := lower) (upper := upper) (payloadType := payloadType)
            witness lowerEvidence upperEvidence payload)
          ready))
      payload := by
  rfl

/-- Transporting a view across equality of binder plans preserves its raw
slot equation. -/
theorem rawSlot_castPlan
    {first second : Interface.BinderPlan []}
    (equal : first = second) (view : EliminationView first)
    (raw : RawSlot view) :
    RawSlot (EliminationView.castPlan equal view) := by
  cases equal
  exact raw

/-- Transporting an exact view across plan equality preserves its payload
equation. -/
theorem memberPayload_castPlan
    {firstLower firstUpper secondLower secondUpper : Ty []}
    {firstPayload secondPayload : Ty ([.tvar])}
    (equal :
      Interface.BinderPlan.exact firstLower firstUpper firstPayload =
        Interface.BinderPlan.exact secondLower secondUpper secondPayload)
    (view : EliminationView
      (.exact firstLower firstUpper firstPayload : Interface.BinderPlan []))
    (expected : Exp []) (payload : MemberPayload view expected) :
    MemberPayload (EliminationView.castPlan equal view) expected := by
  cases equal
  exact payload

/-- The ordinary closed-cast adapter always creates a fresh direct ordinary
view, hence satisfies the raw-slot law independently of its input view. -/
theorem rawSlot_adaptedOrdinary
    {outerPlan : Interface.BinderPlan []}
    (outer : EliminationView outerPlan) (domain : Co [])
    (valueType : Ty []) :
    RawSlot (AdaptedArgument.ordinary outer domain valueType).view := by
  rfl

/-- Reflexive adaptation preserves all slot behavior of its input view. -/
theorem rawSlot_adaptedReflexive
    {outerPlan : Interface.BinderPlan []}
    (outer : EliminationView outerPlan) (ty : Ty [])
    (raw : RawSlot outer) :
    RawSlot (AdaptedArgument.reflexive outer ty).view :=
  raw

/-- Transitive adaptation exposes exactly the second adapter's view. -/
theorem rawSlot_adaptedTrans
    {outerPlan : Interface.BinderPlan []}
    (outer : EliminationView outerPlan) {first second : Co []}
    (firstAdapted : AdaptedArgument first outer)
    (secondAdapted : AdaptedArgument second firstAdapted.view)
    (raw : RawSlot secondAdapted.view) :
    RawSlot
      (AdaptedArgument.trans outer firstAdapted secondAdapted).view :=
  raw

/-- An ordinary source shape makes the generated payload obligation
vacuous, independently of the proof term chosen for well-formedness. -/
theorem newPayloadAgreement_ofOrdinary
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (shape : OrdinaryShape sourceType)
    (environment : ClosingEnv sig [])
    (view : EliminationView
      ((TermTranslation.compileBinder scope sourceWf).plan.subst
        environment.substitution))
    (arguments : ClosedArguments n) :
    NewPayloadAgreement scope sourceWf environment view arguments := by
  cases shape <;> cases sourceWf <;> trivial

/-! ## Closed source-value views -/

/-- The closed view generated for a compiled function is a transported
direct ordinary instantiation, and therefore satisfies `RawSlot`. -/
theorem FunctionSpine.closedView_rawSlot
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {domain : LambdaPFC.Ty n} {sourceBody : LambdaPFC.Tm (n + 1)}
    {sourceType : LambdaPFC.Ty n}
    {sig : Sig} {targetContext : Ctx sig}
    {typing : Fragment.HasType sourceContext (.abs domain sourceBody)
      sourceType}
    (spine : FunctionSpine typing)
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig []) :
    RawSlot (spine.closedView scope environment).view := by
  unfold OperationalValueEvidence.FunctionSpine.closedView
  apply rawSlot_castPlan
  apply rawSlot_ofInstantiation

/-- The direct exact-package compiler produces a raw-slot-coherent view. -/
theorem exactClosedView_rawSlot
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (first : Fin n) (label : LambdaPFC.Name)
    {witness : LambdaPFC.Ty n}
    (witnessWf : Fragment.Wf sourceContext witness)
    (environment : ClosingEnv sig [])
    (payloadReady : Exp.IsValue
      (environment.closeExp
        (translatePath scope
          (Fragment.PathTy.var
            (Γ := sourceContext) (x := first))).expression)) :
    RawSlot
      (OperationalPackageBehavior.exact scope first label witnessWf
        environment payloadReady).view := by
  unfold OperationalPackageBehavior.exact
  apply rawSlot_ofInstantiation

/-- The direct exact-package compiler exposes the closed translation of its
retained first path as the exact binder's payload. -/
theorem exactClosedView_memberPayload
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (first : Fin n) (label : LambdaPFC.Name)
    {witness : LambdaPFC.Ty n}
    (witnessWf : Fragment.Wf sourceContext witness)
    (environment : ClosingEnv sig [])
    (payloadReady : Exp.IsValue
      (environment.closeExp
        (translatePath scope
          (Fragment.PathTy.var
            (Γ := sourceContext) (x := first))).expression)) :
    MemberPayload
      (OperationalPackageBehavior.exact scope first label witnessWf
        environment payloadReady).view
      (environment.closeExp
        (translatePath scope
          (Fragment.PathTy.var
            (Γ := sourceContext) (x := first))).expression) := by
  unfold OperationalPackageBehavior.exact
  apply memberPayload_ofInstantiation

/-- Canonical reflexive package spines preserve the direct package view and
its raw-slot equation. -/
theorem ExactPackageSpine.closedView_rawSlot
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {first : Fin n} {label : LambdaPFC.Name}
    {witness sourceType : LambdaPFC.Ty n}
    {sig : Sig} {targetContext : Ctx sig}
    {typing : Fragment.HasType sourceContext
      (.pair first label (.type witness)) sourceType}
    (spine : ExactPackageSpine typing)
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig [])
    (payloadReady : Exp.IsValue
      (environment.closeExp
        (translatePath scope
          (Fragment.PathTy.var
            (Γ := sourceContext) (x := first))).expression)) :
    RawSlot (spine.closedView scope environment payloadReady).view := by
  induction spine with
  | package witnessWf =>
      exact exactClosedView_rawSlot scope first label witnessWf environment
        payloadReady
  | refl inner ih =>
      exact ih

/-- Canonical reflexive package spines preserve the exact package's payload
equation, phrased through the proof-relevant binder plan selected by the
outer typing derivation. -/
theorem ExactPackageSpine.closedView_newPayload
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {first : Fin n} {label : LambdaPFC.Name}
    {witness sourceType : LambdaPFC.Ty n}
    {sig : Sig} {targetContext : Ctx sig}
    {typing : Fragment.HasType sourceContext
      (.pair first label (.type witness)) sourceType}
    (spine : ExactPackageSpine typing)
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig [])
    (payloadReady : Exp.IsValue
      (environment.closeExp
        (translatePath scope
          (Fragment.PathTy.var
            (Γ := sourceContext) (x := first))).expression)) :
    (arguments : ClosedArguments n) ->
    ClosedPathAgreement scope environment arguments ->
    NewPayloadAgreement scope typing.typeWf environment
      (spine.closedView scope environment payloadReady).view arguments := by
  intro arguments agreement
  induction spine with
  | package witnessWf =>
      have generated := exactClosedView_memberPayload scope first label
        witnessWf environment payloadReady
      exact generated.trans
        (agreement
          (Fragment.PathTy.var
            (Γ := sourceContext) (x := first)))
  | refl inner ih =>
      exact ih

/-- Every closed view generated by the heap-storable value evidence has a
coherent raw projection. -/
theorem ApplicationValueEvidence.closedView_rawSlot
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {term : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext term sourceType}
    (evidence : ApplicationValueEvidence typing)
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig [])
    (ready : evidence.ClosedReady scope environment) :
    RawSlot (evidence.closedView scope environment ready).view := by
  cases evidence with
  | function spine =>
      exact
        OperationalPathCoherenceGenerated.FunctionSpine.closedView_rawSlot
          spine.functionSpine scope environment
  | package spine =>
      exact
        OperationalPathCoherenceGenerated.ExactPackageSpine.closedView_rawSlot
          spine scope environment ready

/-- Every closed view generated by heap-storable value evidence satisfies
the payload law selected by its outer source typing.  The package case uses
the older closed-path agreement to identify its retained first path. -/
theorem ApplicationValueEvidence.closedView_newPayload
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {term : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext term sourceType}
    (evidence : ApplicationValueEvidence typing)
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig [])
    (ready : evidence.ClosedReady scope environment)
    (arguments : ClosedArguments n)
    (agreement : ClosedPathAgreement scope environment arguments) :
    NewPayloadAgreement scope typing.typeWf environment
      (evidence.closedView scope environment ready).view arguments := by
  cases evidence with
  | function spine =>
      exact newPayloadAgreement_ofOrdinary scope _
        spine.functionSpine.targetShape environment
        ((ApplicationValueEvidence.function spine).closedView scope
          environment ready).view arguments
  | package spine =>
      exact
        OperationalPathCoherenceGenerated.ExactPackageSpine.closedView_newPayload
          spine scope environment ready arguments agreement

/-- The whole admissibility predicate exposes the same generated slot laws
after value inversion. -/
theorem OperationallyAdmissible.closedValueView_rawSlot
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {term : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext term sourceType}
    (admissible : OperationallyAdmissible typing)
    (value : LambdaPFC.Tm.IsValue term)
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig [])
    (ready : (admissible.valueEvidence value).ClosedReady scope
      environment) :
    RawSlot
      (admissible.closedValueView value scope environment ready).view :=
  OperationalPathCoherenceGenerated.ApplicationValueEvidence.closedView_rawSlot
    (admissible.valueEvidence value) scope environment ready

/-- Payload counterpart of `closedValueView_rawSlot`. -/
theorem OperationallyAdmissible.closedValueView_newPayload
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {term : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext term sourceType}
    (admissible : OperationallyAdmissible typing)
    (value : LambdaPFC.Tm.IsValue term)
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig [])
    (ready : (admissible.valueEvidence value).ClosedReady scope
      environment)
    (arguments : ClosedArguments n)
    (agreement : ClosedPathAgreement scope environment arguments) :
    NewPayloadAgreement scope typing.typeWf environment
      (admissible.closedValueView value scope environment ready).view
      arguments :=
  OperationalPathCoherenceGenerated.ApplicationValueEvidence.closedView_newPayload
    (admissible.valueEvidence value) scope environment ready arguments
    agreement

/-! ## Packaged local laws and smart store builders -/

/-- The two local path laws needed when a behavioral view is installed as a
new lexical slot. -/
structure BehaviorPathCoherence
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (environment : ClosingEnv sig [])
    (behavior : EliminationView
      ((TermTranslation.compileBinder scope sourceWf).plan.subst
        environment.substitution))
    (arguments : ClosedArguments n) : Prop where
  raw : RawSlot behavior
  payload : NewPayloadAgreement scope sourceWf environment behavior arguments

namespace BehaviorPathCoherence

/-- Package the two laws proved above for a canonical closed source value
view. -/
theorem ofApplicationValueEvidence
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {term : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext term sourceType}
    (evidence : ApplicationValueEvidence typing)
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig [])
    (ready : evidence.ClosedReady scope environment)
    (arguments : ClosedArguments n)
    (agreement : ClosedPathAgreement scope environment arguments) :
    BehaviorPathCoherence scope typing.typeWf environment
      (evidence.closedView scope environment ready).view arguments where
  raw :=
    OperationalPathCoherenceGenerated.ApplicationValueEvidence.closedView_rawSlot
      evidence scope environment ready
  payload :=
    OperationalPathCoherenceGenerated.ApplicationValueEvidence.closedView_newPayload
      evidence scope environment ready arguments agreement

/-- Cast the direct ordinary adaptation to the binder plan chosen by a
source well-formedness derivation. -/
theorem ofAdaptedOrdinary
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (shape : OrdinaryShape sourceType)
    (environment : ClosingEnv sig [])
    {outerPlan : Interface.BinderPlan []}
    (outer : EliminationView outerPlan) (domain : Co [])
    (valueType : Ty [])
    (planEq :
      (Interface.BinderPlan.ordinary valueType) =
        (TermTranslation.compileBinder scope sourceWf).plan.subst
          environment.substitution)
    (arguments : ClosedArguments n) :
    BehaviorPathCoherence scope sourceWf environment
      (EliminationView.castPlan planEq
        (AdaptedArgument.ordinary outer domain valueType).view)
      arguments where
  raw := rawSlot_castPlan planEq _
    (rawSlot_adaptedOrdinary outer domain valueType)
  payload := newPayloadAgreement_ofOrdinary scope sourceWf shape environment
    _ arguments

end BehaviorPathCoherence

/-! The following wrappers keep `StoreEnvironment` unchanged.  Lookup of the
newest and older slots is definitional for each constructor, so callers need
only provide `BehaviorPathCoherence`. -/

/-- Smart path-coherence builder for native allocation plus lexical
extension.  Native value evidence remains independent of the adapted lexical
behavior; the latter's two path laws are supplied by `laws`. -/
theorem storePathCoherence_extend
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {olderClosing : ClosingEnv sig []}
    {older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope olderClosing}
    (coherent : StorePathCoherence older)
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
      (storeArguments older)) :
    StorePathCoherence
      (StoreEnvironment.extend older typing native nativeValuation
        nativeAdmissible nativeEvidence nativeEnvironment nativeReady
        runtimeReady runtime_eq memberCell functionCell behavior
        normalizes) := by
  apply OperationalPathCoherence.StorePathCoherence.extend coherent
    typing.typeWf behavior laws.raw laws.payload
  · rfl
  · intro index
    rfl

/-- Smart path-coherence builder for a lexical path alias. -/
theorem storePathCoherence_alias
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {olderClosing : ClosingEnv sig []}
    {older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope olderClosing}
    (coherent : StorePathCoherence older)
    {path : LambdaPFC.Path lexical}
    {sourceType : LambdaPFC.Ty lexical}
    (typing : Fragment.HasType sourceContext (.path path) sourceType)
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
    StorePathCoherence
      (StoreEnvironment.alias older typing memberCell functionCell behavior
        normalizes) := by
  apply OperationalPathCoherence.StorePathCoherence.extend coherent
    typing.typeWf behavior laws.raw laws.payload
  · rfl
  · intro index
    rfl

/-- Smart path-coherence builder for binding an existing native location. -/
theorem storePathCoherence_bindLocation
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {olderClosing : ClosingEnv sig []}
    {older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope olderClosing}
    (coherent : StorePathCoherence older)
    {sourceType : LambdaPFC.Ty lexical}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (location : Fin current)
    {runtimeValue : LambdaPFC.Tm current}
    (binds : LambdaPFC.Store.Binds sourceStore location runtimeValue)
    (compiled : CompiledBinding runtimeValue)
    {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
    {nativeScope : Scope compiled.native.context nativeTargetContext}
    {nativeClosing : ClosingEnv nativeSig []}
    (nativeEnvironment : StoreEnvironment compiled.native.context sourceStore
      compiled.nativeValuation nativeTargetContext nativeScope nativeClosing)
    (memberCell : MemberCell sourceType sourceStore valuation location)
    (functionCell : FunctionCell sourceType sourceStore valuation location)
    (behavior : EliminationView
      ((TermTranslation.compileBinder scope sourceWf).plan.subst
        olderClosing.substitution))
    (laws : BehaviorPathCoherence scope sourceWf olderClosing behavior
      (storeArguments older)) :
    StorePathCoherence
      (StoreEnvironment.bindLocation older sourceWf location binds compiled
        nativeEnvironment memberCell functionCell behavior) := by
  apply OperationalPathCoherence.StorePathCoherence.extend coherent sourceWf
    behavior laws.raw laws.payload
  · rfl
  · intro index
    rfl

end OperationalPathCoherenceGenerated
end LambdaPToFCo
