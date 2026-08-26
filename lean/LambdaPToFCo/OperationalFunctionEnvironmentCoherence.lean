import LambdaPToFCo.OperationalFunctionResultProvenance

/-!
# Function provenance for compiled lexical environments

`StoreEnvironment` deliberately separates a lexical slot from the physical
cell to which the slot points.  This module records the corresponding
function invariant without changing either representation: whenever a
lexical slot advertises an arrow, lookup returns wrapper-aware target
function evidence together with the retained source abstraction and its
native source environment.

The structural alignment in `FunctionBindingWitness` is the exact boundary
between those two views.  It identifies the source store, runtime value, and
native environment retained by `SourceFunctionClosure` with the ones returned
by physical lookup.  A higher recursive coherence layer can therefore
transport its native-environment invariant to the recovered source closure
without introducing an import cycle here.

Only direct allocation may introduce a new arrow slot.  The restricted alias
and existing-location builders below require `NonCanonicalResultShape`, so
their newest arrow case is impossible and all older witnesses are preserved.
-/

namespace LambdaPToFCo
namespace OperationalFunctionEnvironmentCoherence

open SystemFCo
open StaticTranslation
open OperationalCode
open OperationalEnvironment
open OperationalBindingView
open OperationalStoreEnvironment
open OperationalAdmissibility
open OperationalApplicationSpine
open OperationalFunctionResultProvenance

private def castRuntimeValue
    {left right : Nat} (equal : left = right)
    (value : LambdaPFC.Tm right) : LambdaPFC.Tm left :=
  equal.symm ▸ value

private theorem castRuntimeValue_ready
    {left right : Nat} (equal : left = right)
    {value : LambdaPFC.Tm right} (ready : value.IsValue) :
    (castRuntimeValue equal value).IsValue := by
  cases equal
  exact ready

/-- Structural alignment between a retained source function closure and the
physical binding returned by store lookup.  The direct constructor states
that both views are literally the same origin.  `nativeWeaken` advances them
through one unrelated allocation in lockstep.

Using a structural relation here is important: heterogeneous equality alone
does not support dependent congruence through `StoreEnvironment.nativeWeaken`
when the native source and target indices are abstract. -/
inductive FunctionClosureAlignment {behavior : Exp []} :
    (closure : SourceFunctionClosure behavior) ->
    {current : Nat} ->
    (sourceStore : LambdaPFC.Store current) ->
    (runtimeValue : LambdaPFC.Tm current) ->
    {nativeLexical : Nat} ->
    {nativeContext : LambdaPFC.Ctx nativeLexical} ->
    {nativeValuation : SourceValuation nativeLexical current} ->
    {nativeSig : Sig} -> {nativeTargetContext : Ctx nativeSig} ->
    {nativeScope : Scope nativeContext nativeTargetContext} ->
    {nativeClosing : ClosingEnv nativeSig []} ->
    (nativeEnvironment : StoreEnvironment nativeContext sourceStore
      nativeValuation nativeTargetContext nativeScope nativeClosing) ->
    Type where
  | direct (closure : SourceFunctionClosure behavior) :
      FunctionClosureAlignment closure closure.sourceStore
        closure.runtimeValue closure.nativeEnvironment
  | nativeWeaken
      {closure : SourceFunctionClosure behavior}
      {current : Nat}
      {sourceStore : LambdaPFC.Store current}
      {runtimeValue : LambdaPFC.Tm current}
      {nativeLexical : Nat}
      {nativeContext : LambdaPFC.Ctx nativeLexical}
      {nativeValuation : SourceValuation nativeLexical current}
      {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
      {nativeScope : Scope nativeContext nativeTargetContext}
      {nativeClosing : ClosingEnv nativeSig []}
      {nativeEnvironment : StoreEnvironment nativeContext sourceStore
        nativeValuation nativeTargetContext nativeScope nativeClosing}
      (older : FunctionClosureAlignment closure sourceStore runtimeValue
        nativeEnvironment)
      (allocatedValue : LambdaPFC.Tm current)
      (allocatedReady : allocatedValue.IsValue)
      (current_eq : closure.current = current) :
      FunctionClosureAlignment
        (closure.nativeWeaken (castRuntimeValue current_eq allocatedValue)
          (castRuntimeValue_ready current_eq allocatedReady))
        (.val sourceStore allocatedValue allocatedReady)
        runtimeValue.weaken
        (nativeEnvironment.nativeWeaken allocatedValue allocatedReady)

namespace FunctionClosureAlignment

/-- Aligned physical data necessarily has the same store scope as the
retained source closure. -/
theorem current_eq
    {closure : SourceFunctionClosure behavior}
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeValue : LambdaPFC.Tm current}
    {nativeLexical : Nat}
    {nativeContext : LambdaPFC.Ctx nativeLexical}
    {nativeValuation : SourceValuation nativeLexical current}
    {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
    {nativeScope : Scope nativeContext nativeTargetContext}
    {nativeClosing : ClosingEnv nativeSig []}
    {nativeEnvironment : StoreEnvironment nativeContext sourceStore
      nativeValuation nativeTargetContext nativeScope nativeClosing}
    (alignment : FunctionClosureAlignment closure sourceStore runtimeValue
      nativeEnvironment) :
    closure.current = current := by
  cases alignment with
  | direct => rfl
  | nativeWeaken _ _ _ current_eq => exact congrArg (fun n => n + 1) current_eq

/-- Changing only the wrapper-aware target image preserves the complete
physical source-closure alignment. -/
noncomputable def withImage
    {closure : SourceFunctionClosure oldBehavior}
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeValue : LambdaPFC.Tm current}
    {nativeLexical : Nat}
    {nativeContext : LambdaPFC.Ctx nativeLexical}
    {nativeValuation : SourceValuation nativeLexical current}
    {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
    {nativeScope : Scope nativeContext nativeTargetContext}
    {nativeClosing : ClosingEnv nativeSig []}
    {nativeEnvironment : StoreEnvironment nativeContext sourceStore
      nativeValuation nativeTargetContext nativeScope nativeClosing}
    (alignment : FunctionClosureAlignment closure sourceStore runtimeValue
      nativeEnvironment)
    (image : OperationalFunctionPathSpine.NativeFunctionImage newBehavior)
    (plan_eq : image.plan = closure.image.plan)
    (body_heq : HEq image.body closure.image.body)
    (argumentRaw :
      {outerPlan : Interface.BinderPlan []} ->
      (outer : EliminationView outerPlan) ->
      (outerPlan_eq : outerPlan = image.domainPlan) ->
      OperationalPathCoherence.RawSlot outer ->
      OperationalPathCoherence.RawSlot
        ((image.argumentEvidence outer
          outerPlan_eq).toArgumentView.elimination)) :
    FunctionClosureAlignment
      (closure.withImage image plan_eq body_heq argumentRaw)
      sourceStore runtimeValue nativeEnvironment := by
  induction alignment with
  | direct => exact .direct _
  | nativeWeaken older allocatedValue allocatedReady current_eq ih =>
      exact .nativeWeaken (ih plan_eq body_heq) allocatedValue
        allocatedReady current_eq

end FunctionClosureAlignment

/-- Wrapper-aware function provenance aligned with one physical binding.

The lexical scope, closing environment, and view describe the current slot.
The native environment may have completely different source and target
indices; the heterogeneous equalities connect the retained source closure to
that physical origin without conflating the two scopes. -/
structure FunctionBindingWitness
    {lexical : Nat} {sourceContext : LambdaPFC.Ctx lexical}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (closing : ClosingEnv sig [])
    {plan : Interface.BinderPlan []} (view : EliminationView plan)
    (domain : LambdaPFC.Ty lexical)
    {current : Nat} (sourceStore : LambdaPFC.Store current)
    (runtimeValue : LambdaPFC.Tm current)
    {nativeLexical : Nat}
    {nativeContext : LambdaPFC.Ctx nativeLexical}
    {nativeValuation : SourceValuation nativeLexical current}
    {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
    {nativeScope : Scope nativeContext nativeTargetContext}
    {nativeClosing : ClosingEnv nativeSig []}
    (nativeEnvironment : StoreEnvironment nativeContext sourceStore
      nativeValuation nativeTargetContext nativeScope nativeClosing) : Type
    where
  domainWf : Fragment.Wf sourceContext domain
  provenance : FunctionResultProvenance scope domainWf closing view
  alignment : FunctionClosureAlignment provenance.closure sourceStore
    runtimeValue nativeEnvironment

namespace FunctionBindingWitness

/-- One unrelated physical allocation weakens the retained source closure in
lockstep with the binding returned by store lookup.  Lexical target behavior
is closed already and therefore does not change. -/
noncomputable def nativeWeaken
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    {plan : Interface.BinderPlan []} {view : EliminationView plan}
    {domain : LambdaPFC.Ty lexical}
    {sourceStore : LambdaPFC.Store current}
    {runtimeValue : LambdaPFC.Tm current}
    {nativeLexical : Nat}
    {nativeContext : LambdaPFC.Ctx nativeLexical}
    {nativeValuation : SourceValuation nativeLexical current}
    {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
    {nativeScope : Scope nativeContext nativeTargetContext}
    {nativeClosing : ClosingEnv nativeSig []}
    {nativeEnvironment : StoreEnvironment nativeContext sourceStore
      nativeValuation nativeTargetContext nativeScope nativeClosing}
    (witness : FunctionBindingWitness scope closing view domain sourceStore
      runtimeValue nativeEnvironment)
    (allocatedValue : LambdaPFC.Tm current)
    (allocatedReady : allocatedValue.IsValue) :
    FunctionBindingWitness (current := current + 1)
      (nativeValuation := nativeValuation.weaken) scope closing view domain
      (@LambdaPFC.Store.val current sourceStore allocatedValue allocatedReady)
      runtimeValue.weaken
      (@StoreEnvironment.nativeWeaken nativeLexical current nativeContext
        sourceStore nativeValuation nativeSig nativeTargetContext nativeScope
        nativeClosing nativeEnvironment allocatedValue allocatedReady) := by
  let current_eq := witness.alignment.current_eq
  exact
    { domainWf := witness.domainWf
      provenance :=
        { closure := witness.provenance.closure.nativeWeaken
            (castRuntimeValue current_eq allocatedValue)
            (castRuntimeValue_ready current_eq allocatedReady)
          domainPlan_eq := witness.provenance.domainPlan_eq }
      alignment := witness.alignment.nativeWeaken allocatedValue
        allocatedReady current_eq }

/-- Re-expose an aligned source closure through a different target function
wrapper.  The caller supplies the new closed domain-plan equation; the native
store, runtime value, source body, and native environment remain unchanged. -/
noncomputable def withImage
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    {oldPlan newPlan : Interface.BinderPlan []}
    {oldView : EliminationView oldPlan}
    {newView : EliminationView newPlan}
    {domain : LambdaPFC.Ty lexical}
    {sourceStore : LambdaPFC.Store current}
    {runtimeValue : LambdaPFC.Tm current}
    {nativeLexical : Nat}
    {nativeContext : LambdaPFC.Ctx nativeLexical}
    {nativeValuation : SourceValuation nativeLexical current}
    {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
    {nativeScope : Scope nativeContext nativeTargetContext}
    {nativeClosing : ClosingEnv nativeSig []}
    {nativeEnvironment : StoreEnvironment nativeContext sourceStore
      nativeValuation nativeTargetContext nativeScope nativeClosing}
    (witness : FunctionBindingWitness scope closing oldView domain sourceStore
      runtimeValue nativeEnvironment)
    (image : OperationalFunctionPathSpine.NativeFunctionImage
      newView.argument)
    (plan_eq : image.plan = witness.provenance.closure.image.plan)
    (body_heq : HEq image.body witness.provenance.closure.image.body)
    (argumentRaw :
      {outerPlan : Interface.BinderPlan []} ->
      (outer : EliminationView outerPlan) ->
      (outerPlan_eq : outerPlan = image.domainPlan) ->
      OperationalPathCoherence.RawSlot outer ->
      OperationalPathCoherence.RawSlot
        ((image.argumentEvidence outer
          outerPlan_eq).toArgumentView.elimination))
    (domainPlan_eq :
      OperationalApplicationSpine.closedPlan scope closing witness.domainWf =
        image.domainPlan) :
    FunctionBindingWitness scope closing newView domain sourceStore
      runtimeValue nativeEnvironment where
  domainWf := witness.domainWf
  provenance :=
    { closure := witness.provenance.closure.withImage image plan_eq body_heq
        argumentRaw
      domainPlan_eq := domainPlan_eq }
  alignment := witness.alignment.withImage image plan_eq body_heq argumentRaw

end FunctionBindingWitness

/-- The function witness required at one lexical lookup.  The source arrow
equality is kept as an index so callers cannot ask for provenance at an
unrelated domain. -/
abbrev LookupFunctionWitness
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (index : Fin lexical)
    {domain codomain : LambdaPFC.Ty
      (environment.lookup index).slot.arity}
    (_typeEq : (environment.lookup index).slot.sourceType =
      .Fun domain codomain.weaken) : Type :=
  FunctionBindingWitness
    (environment.lookup index).slot.scope
    (environment.lookup index).slot.environment
    (environment.lookup index).slot.behavior domain sourceStore
    (environment.lookup index).runtimeValue
    (environment.lookup index).nativeEnvironment

/-- Conditional function evidence at one lookup.  Factoring this dependent
function out is what lets environment builders split the lexical index before
the domain and codomain (which live in that slot's retained source arity) are
introduced. -/
structure SlotFunctionInvariant
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (index : Fin lexical) : Prop where
  function :
    {domain codomain : LambdaPFC.Ty
      (environment.lookup index).slot.arity} ->
    (typeEq : (environment.lookup index).slot.sourceType =
      .Fun domain codomain.weaken) ->
    Nonempty (LookupFunctionWitness environment index typeEq)

/-- Every arrow-typed lexical slot has wrapper-aware function provenance
aligned with the physical binding returned by lookup. -/
structure FunctionEnvironmentCoherence
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing) : Type where
  slots : (index : Fin lexical) ->
    SlotFunctionInvariant environment index

namespace FunctionEnvironmentCoherence

/-- The empty environment has no lexical function slots. -/
def initial : FunctionEnvironmentCoherence StoreEnvironment.initial where
  slots index := Fin.elim0 index

/-- Recover wrapper-aware source/target function provenance at one retained
lexical slot. -/
theorem lookupFunction
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    {environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing}
    (coherent : FunctionEnvironmentCoherence environment)
    (index : Fin lexical)
    {domain codomain : LambdaPFC.Ty
      (environment.lookup index).slot.arity}
    (typeEq : (environment.lookup index).slot.sourceType =
      .Fun domain codomain.weaken) :
    Nonempty (LookupFunctionWitness environment index typeEq) :=
  (coherent.slots index).function typeEq

/-- Function provenance survives a physical allocation hidden from the
lexical source and target scopes. -/
noncomputable def nativeWeaken
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    {environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing}
    (coherent : FunctionEnvironmentCoherence environment)
    (allocatedValue : LambdaPFC.Tm current)
    (allocatedReady : allocatedValue.IsValue) :
    FunctionEnvironmentCoherence
      (environment.nativeWeaken allocatedValue allocatedReady) where
  slots := fun index =>
    { function := fun typeEq => by
        rcases coherent.lookupFunction index typeEq with ⟨witness⟩
        exact ⟨witness.nativeWeaken allocatedValue allocatedReady⟩ }

/-- Direct native allocation is the only builder which may install a fresh
arrow slot.  The supplied newest witness describes the value before it is
inserted into the immutable store; both newest and older physical bindings
are weakened once by the allocation. -/
noncomputable def extend
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {olderClosing : ClosingEnv sig []}
    {older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope olderClosing}
    (olderCoherent : FunctionEnvironmentCoherence older)
    {sourceTerm : LambdaPFC.Tm lexical}
    {sourceType : LambdaPFC.Ty lexical}
    (typing : Fragment.HasType sourceContext sourceTerm sourceType)
    (native : TypedCode)
    (nativeValuation : SourceValuation native.arity current)
    (nativeAdmissible : OperationalAdmissibility.OperationallyAdmissible
      native.typing)
    (nativeEvidence : OperationalApplicationSpine.ApplicationValueEvidence
      native.typing)
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
    (newest :
      {domain codomain : LambdaPFC.Ty lexical} ->
      sourceType = .Fun domain codomain.weaken ->
      Nonempty
        (FunctionBindingWitness scope olderClosing behavior domain sourceStore
          runtimeValue nativeEnvironment)) :
    FunctionEnvironmentCoherence
      (StoreEnvironment.extend older typing native nativeValuation
        nativeAdmissible nativeEvidence nativeEnvironment nativeReady
        runtimeReady runtime_eq memberCell functionCell behavior
        normalizes) where
  slots := fun index => by
    refine Fin.cases ?_ (fun olderIndex => ?_) index
    · exact
        { function := fun typeEq => by
            rcases newest typeEq with ⟨witness⟩
            exact ⟨witness.nativeWeaken runtimeValue runtimeReady⟩ }
    · exact
        { function := fun typeEq => by
            rcases olderCoherent.lookupFunction olderIndex typeEq with
              ⟨witness⟩
            exact ⟨witness.nativeWeaken runtimeValue runtimeReady⟩ }

/-- A restricted noncanonical path alias cannot introduce an arrow slot.
Every older lexical witness is reused unchanged because no physical
allocation occurs. -/
noncomputable def aliasNonCanonical
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {olderClosing : ClosingEnv sig []}
    {older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope olderClosing}
    (olderCoherent : FunctionEnvironmentCoherence older)
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
      behavior.argument) :
    FunctionEnvironmentCoherence
      (StoreEnvironment.alias older typing memberCell functionCell behavior
        normalizes) where
  slots := fun index => by
    refine Fin.cases ?_ (fun olderIndex => ?_) index
    · exact
        { function := fun typeEq =>
            (shape.notArrow
              { domain := _
                codomain := _
                equality := typeEq }).elim }
    · exact
        { function := fun typeEq =>
            olderCoherent.lookupFunction olderIndex typeEq }

/-- Binding an existing physical location at a noncanonical result type also
cannot introduce an arrow slot.  Older function provenance is preserved
verbatim. -/
noncomputable def bindLocationNonCanonical
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {olderClosing : ClosingEnv sig []}
    {older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope olderClosing}
    (olderCoherent : FunctionEnvironmentCoherence older)
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
    (memberCell : MemberCell sourceType sourceStore valuation location)
    (functionCell : FunctionCell sourceType sourceStore valuation location)
    (behavior : EliminationView
      ((TermTranslation.compileBinder scope sourceWf).plan.subst
        olderClosing.substitution)) :
    FunctionEnvironmentCoherence
      (StoreEnvironment.bindLocation older sourceWf location binds compiled
        nativeEnvironment memberCell functionCell behavior) where
  slots := fun index => by
    refine Fin.cases ?_ (fun olderIndex => ?_) index
    · exact
        { function := fun typeEq =>
            (shape.notArrow
              { domain := _
                codomain := _
                equality := typeEq }).elim }
    · exact
        { function := fun typeEq =>
            olderCoherent.lookupFunction olderIndex typeEq }

end FunctionEnvironmentCoherence

end OperationalFunctionEnvironmentCoherence
end LambdaPToFCo
