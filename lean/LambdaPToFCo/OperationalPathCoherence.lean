import LambdaPToFCo.OperationalStoreEnvironment

/-!
# Closed target coherence of lexical source paths

Closing a translated source variable should expose the behavioral argument
installed for that lexical slot.  For an exact first projection, closing the
package's payload projection should expose the argument installed for its
statically retained `first` slot.

Neither fact follows from the bare `EliminationView` interface: its
substitution is intentionally abstract.  This module isolates the two small
slot laws required by a store-level path-coherence invariant, without adding
them to `StoreEnvironment` itself.
-/

namespace LambdaPToFCo
namespace OperationalPathCoherence

open SystemFCo
open StaticTranslation
open OperationalCode
open OperationalBindingView
open OperationalStoreEnvironment

/-! ## Coherence of one closed binder view -/

/-- The raw source-variable projection introduced by a binder plan.  For an
ordinary plan it is the sole term variable; for an exact plan it is the
oldest of the five interface slots. -/
def binderRawExpression :
    (plan : Interface.BinderPlan sig) -> Exp plan.scope
  | .ordinary _ => .var .here
  | .exact _ _ _ => .var (.there (.there (.there (.there .here))))

/-- The behavioral substitution maps the freshly introduced raw projection
back to the argument which the view advertises. -/
def RawSlot
    {plan : Interface.BinderPlan []}
    (view : EliminationView plan) : Prop :=
  (binderRawExpression plan).subst view.substitution = view.argument

/-- For an exact binder, the newest term-variable projection is its exposed
payload. -/
def MemberPayload
    {lower upper : Ty []} {payloadType : Ty ([.tvar])}
    (view : EliminationView
      (.exact lower upper payloadType : Interface.BinderPlan []))
    (expected : Exp []) : Prop :=
  (Exp.var (.here : BVar
      (Interface.BinderPlan.exact lower upper payloadType).scope .var)).subst
      view.substitution = expected

/-! ## Structural closure through one later binder -/

/-- A closed expression is unaffected by renaming into an arbitrary mixed
scope and substituting that scope back to the empty signature. -/
theorem closed_rename_subst
    (expression : Exp []) (rename : Rename [] sig)
    (substitution : Subst sig []) :
    (expression.rename rename).subst substitution = expression := by
  rw [Exp.rename_asSubst, Exp.subst_comp]
  have cancel : rename.asSubst.comp substitution = Subst.id := by
    apply Subst.funext <;> intro index <;> cases index
  rw [cancel, Exp.subst_id]

/-- The plan's old-scope inclusion commutes with simultaneous closure of the
old scope. -/
theorem rename_weaken_subst_scope
    (expression : Exp sig)
    (plan : Interface.BinderPlan sig)
    (substitution : Subst sig []) :
    (expression.rename plan.weaken).subst
        (plan.scopeSubst substitution) =
      (expression.subst substitution).rename
        (plan.subst substitution).weaken := by
  cases plan with
  | ordinary valueType =>
      exact (expression.weaken_subst_comm_base substitution).symm
  | exact lower upper payloadType =>
      simp only [Interface.BinderPlan.weaken,
        Interface.BinderPlan.scopeSubst, Interface.BinderPlan.subst_exact,
        ← Exp.rename_comp]
      change
        (((((expression.weaken .var).weaken .tvar).weaken .cvar).weaken
                .cvar).weaken .var).subst
            (((((substitution.lift .var).lift .tvar).lift .cvar).lift
                .cvar).lift .var) =
          (((((expression.subst substitution).weaken .var).weaken
              .tvar).weaken .cvar).weaken .cvar).weaken .var
      rw [← Exp.weaken_subst_comm_base,
        ← Exp.weaken_subst_comm_base,
        ← Exp.weaken_subst_comm_base,
        ← Exp.weaken_subst_comm_base,
        ← Exp.weaken_subst_comm_base]

/-- Closing a projection renamed through one later binder yields the same
closed expression as before the extension.  This fact is independent of the
new binder's behavioral substitution. -/
theorem close_old_expression
    (environment : OperationalEnvironment.ClosingEnv sig [])
    (plan : Interface.BinderPlan sig)
    (view : EliminationView
      (plan.subst environment.substitution))
    (expression : Exp sig) :
    (extendClosing environment plan view).closeExp
        (expression.rename plan.weaken) =
      environment.closeExp expression := by
  rw [OperationalEnvironment.ClosingEnv.closeExp, extendClosing,
    OperationalEnvironment.ClosingEnv.closeExp, ← Exp.subst_comp,
    rename_weaken_subst_scope]
  exact closed_rename_subst (expression.subst environment.substitution)
    (plan.subst environment.substitution).weaken view.substitution

/-- Renaming a typed interface slot renames the expression selected as its
source-path projection. -/
theorem path_rename_expression
    (slot : TypedInterfaceSlot sourceContext)
    (typed : Rename.Typed sourceContext targetContext rename) :
    ((slot.rename typed).path).expression =
      slot.path.expression.rename rename := by
  cases slot <;> rfl

/-- Renaming an exact slot renames its payload projection. -/
theorem payload_rename_expression
    (slot : TypedExactSlot sourceContext)
    (typed : Rename.Typed sourceContext targetContext rename) :
    ((slot.rename typed).payloadPath).expression =
      slot.payloadPath.expression.rename rename := rfl

/-- Translation of an older variable through one compiled source binder is
exactly target renaming through that binder plan. -/
theorem translatePath_old_var_expression
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (index : Fin n) :
    (translatePath
        (TermTranslation.compileBinder scope sourceWf).extended
        (Fragment.PathTy.var
          (Γ := sourceContext.snoc sourceType) (x := index.succ))).expression =
      (translatePath scope
        (Fragment.PathTy.var
          (Γ := sourceContext) (x := index))).expression.rename
        (TermTranslation.compileBinder scope sourceWf).plan.weaken := by
  cases sourceWf <;>
    simp only [TermTranslation.compileBinder, Scope.bindOrdinary,
      Scope.bindMember, translatePath, Scope.lookup_there_ordinary,
      Scope.lookup_there_member, path_rename_expression]

/-- Translation of an older exact first projection through one compiled
source binder is target renaming through that binder plan. -/
theorem translatePath_old_exactFst_expression
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    {package first : Fin n} {label : LambdaPFC.Name}
    {lower upper : LambdaPFC.Ty n}
    (member : Fragment.BoundMember sourceContext package label lower upper
      first) :
    (translatePath
        (TermTranslation.compileBinder scope sourceWf).extended
        (Fragment.PathTy.exactFst (.there member))).expression =
      (translatePath scope
        (Fragment.PathTy.exactFst member)).expression.rename
        (TermTranslation.compileBinder scope sourceWf).plan.weaken := by
  cases sourceWf <;>
    simp only [TermTranslation.compileBinder, Scope.bindOrdinary,
      Scope.bindMember, translatePath, Scope.lookupMember_there_ordinary,
      Scope.lookupMember_there_member, payload_rename_expression]

/-! ## The newest variable equation -/

/-- Closing the target projection for a freshly extended source variable is
exactly application of the view substitution to that binder's raw slot. -/
theorem close_new_var
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (olderClosing : OperationalEnvironment.ClosingEnv sig [])
    (behavior : EliminationView
      ((TermTranslation.compileBinder scope sourceWf).plan.subst
        olderClosing.substitution))
    (raw : RawSlot behavior) :
    (extendClosing olderClosing
        (TermTranslation.compileBinder scope sourceWf).plan behavior).closeExp
      (translatePath
        (TermTranslation.compileBinder scope sourceWf).extended
        (Fragment.PathTy.var
          (Γ := sourceContext.snoc sourceType) (x := 0))).expression =
      behavior.argument := by
  cases sourceWf <;>
    simpa only [TermTranslation.compileBinder, Scope.bindOrdinary,
      Scope.bindMember, translatePath,
      Scope.lookup_here_ordinary, Scope.lookup_here_member,
      TypedInterfaceSlot.path, newestOrdinary, newestExact,
      Interface.BinderPlan.ordinarySlot, Interface.BinderPlan.exactSlot,
      Interface.OrdinarySlot.rename, Interface.ExactSlot.rename,
      binderRawExpression, Interface.BinderPlan.scopeSubst,
      OperationalEnvironment.ClosingEnv.closeExp, extendClosing,
      Exp.subst, Subst.comp, Subst.lift_var_here,
      Subst.lift_var_there] using raw

/-! ## The newest exact-member payload equation -/

/-- Closing the target payload projection for a freshly introduced exact
member package exposes precisely the expression selected by its payload
substitution component. -/
theorem close_new_exactFst
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (first : Fin n) (label : LambdaPFC.Name)
    {lower upper : LambdaPFC.Ty n}
    (lowerWf : Fragment.Wf sourceContext lower)
    (upperWf : Fragment.Wf sourceContext upper)
    (nonempty : Fragment.Sub sourceContext lower upper)
    (olderClosing : OperationalEnvironment.ClosingEnv sig [])
    (behavior : EliminationView
      ((Interface.BinderPlan.exact
        (translateType scope lowerWf)
        (translateType scope upperWf)
        (payloadFamily (scope.lookup first).path.targetType)).subst
          olderClosing.substitution))
    (expected : Exp [])
    (payload : MemberPayload behavior expected) :
    (extendClosing olderClosing
        (Interface.BinderPlan.exact
          (translateType scope lowerWf)
          (translateType scope upperWf)
          (payloadFamily (scope.lookup first).path.targetType))
        behavior).closeExp
      (translatePath
        (scope.bindMember first label lowerWf upperWf nonempty)
        (Fragment.PathTy.exactFst
          (Fragment.BoundMember.here
            (Γ := sourceContext) (first := first) (label := label)
            (lower := lower) (upper := upper)))).expression =
      expected := by
  simpa only [Scope.bindMember, translatePath, Scope.lookupMember_here,
    TypedExactSlot.payloadPath, newestExact,
    Interface.BinderPlan.exactSlot, Interface.ExactSlot.rename,
    MemberPayload, Interface.BinderPlan.scopeSubst,
    OperationalEnvironment.ClosingEnv.closeExp, extendClosing,
    Exp.subst, Subst.comp, Subst.lift_var_here] using payload

/-! ## A scope-level path image -/

/-- Closed target arguments assigned to the source variables of a scope. -/
abbrev ClosedArguments (arity : Nat) := Fin arity -> Exp []

/-- Add the newest behavioral argument to a family of older closed
arguments. -/
def ClosedArguments.extend (older : ClosedArguments n)
    (newest : Exp []) : ClosedArguments (n + 1) :=
  Fin.cases newest older

/-- Every supported translated path closes to the target argument assigned
to its static store referent. -/
def ClosedPathAgreement
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (closing : OperationalEnvironment.ClosingEnv sig [])
    (arguments : ClosedArguments n) : Prop :=
  forall {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n},
    (typing : Fragment.PathTy sourceContext path sourceType) ->
      closing.closeExp (translatePath scope typing).expression =
        arguments (pathReferentIndex typing)

/-- The extra payload equation required only when the new source binder is
an exact member package.  Ordinary source binders have no payload
projection. -/
def NewPayloadAgreement
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (closing : OperationalEnvironment.ClosingEnv sig [])
    (behavior : EliminationView
      ((TermTranslation.compileBinder scope sourceWf).plan.subst
        closing.substitution))
    (arguments : ClosedArguments n) : Prop :=
  match sourceWf with
  | @Fragment.Wf.memberPackage _ _ first _ _ _ _ _ _ =>
      MemberPayload behavior (arguments first)
  | _ => True

/-- `RawSlot` plus the exact-member payload law are precisely the local
premises needed to extend closed path agreement through one compiled
binder. -/
theorem ClosedPathAgreement.extend
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : OperationalEnvironment.ClosingEnv sig []}
    {arguments : ClosedArguments n}
    (older : ClosedPathAgreement scope closing arguments)
    {sourceType : LambdaPFC.Ty n}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (behavior : EliminationView
      ((TermTranslation.compileBinder scope sourceWf).plan.subst
        closing.substitution))
    (raw : RawSlot behavior)
    (payload : NewPayloadAgreement scope sourceWf closing behavior
      arguments) :
    ClosedPathAgreement
      (TermTranslation.compileBinder scope sourceWf).extended
      (extendClosing closing
        (TermTranslation.compileBinder scope sourceWf).plan behavior)
      (arguments.extend behavior.argument) := by
  intro path pathType typing
  cases typing with
  | @var index =>
      cases index using Fin.cases with
      | zero =>
          simpa only [ClosedArguments.extend, Fin.cases_zero,
            pathReferentIndex_var] using
            close_new_var scope sourceWf closing behavior raw
      | succ olderIndex =>
          let oldTyping := Fragment.PathTy.var
            (Γ := sourceContext) (x := olderIndex)
          have translated := translatePath_old_var_expression scope sourceWf
            olderIndex
          have renamed := congrArg
            (extendClosing closing
              (TermTranslation.compileBinder scope sourceWf).plan behavior).closeExp
            translated
          simpa only [ClosedArguments.extend, Fin.cases_succ,
            pathReferentIndex_var] using
            renamed.trans
              ((close_old_expression closing _ behavior
                (translatePath scope oldTyping).expression).trans
                (older oldTyping))
  | @exactFst package first label lower upper member =>
      cases package using Fin.cases with
      | zero =>
          have memberTypeEq := member.lookup_eq
          change sourceType.weaken =
            Fragment.memberPackageTy first label lower upper at memberTypeEq
          cases sourceWf with
          | top => cases memberTypeEq
          | singleton pathTyping => cases memberTypeEq
          | selection selected nonempty => cases memberTypeEq
          | arrow domainWf codomainWf => cases memberTypeEq
          | @memberPackage storedFirst storedLabel storedLower storedUpper
              lowerWf upperWf nonempty =>
              have storedEq :
                  Fragment.memberPackageTy storedFirst.succ storedLabel
                      storedLower.weaken storedUpper.weaken =
                    Fragment.memberPackageTy first label lower upper := by
                rw [← memberTypeEq]
                exact (Fragment.memberPackageTy_rename storedFirst
                  storedLabel storedLower storedUpper
                  LambdaPFC.FinFun.weaken).symm
              have parts := Fragment.memberPackageTy_injective storedEq
              let newest := Fragment.BoundMember.here
                (Γ := sourceContext) (first := storedFirst)
                (label := storedLabel) (lower := storedLower)
                (upper := storedUpper)
              have slotEq := Scope.lookupMember_irrel
                (TermTranslation.compileBinder scope
                  (Fragment.Wf.memberPackage lowerWf upperWf
                    nonempty)).extended
                member newest
              have translated :
                  (translatePath
                      (TermTranslation.compileBinder scope
                        (Fragment.Wf.memberPackage lowerWf upperWf
                          nonempty)).extended
                      (Fragment.PathTy.exactFst member)).expression =
                    (translatePath
                      (TermTranslation.compileBinder scope
                        (Fragment.Wf.memberPackage lowerWf upperWf
                          nonempty)).extended
                      (Fragment.PathTy.exactFst newest)).expression := by
                exact congrArg
                  (fun slot => slot.payloadPath.expression) slotEq
              have closed := congrArg
                (extendClosing closing
                  (TermTranslation.compileBinder scope
                    (Fragment.Wf.memberPackage lowerWf upperWf
                      nonempty)).plan behavior).closeExp
                translated
              have payload' : MemberPayload behavior
                  (arguments storedFirst) := by
                simpa only [NewPayloadAgreement] using payload
              calc
                _ = (extendClosing closing
                      (TermTranslation.compileBinder scope
                        (Fragment.Wf.memberPackage lowerWf upperWf
                          nonempty)).plan behavior).closeExp
                    (translatePath
                      (TermTranslation.compileBinder scope
                        (Fragment.Wf.memberPackage lowerWf upperWf
                          nonempty)).extended
                      (Fragment.PathTy.exactFst newest)).expression := closed
                _ = arguments storedFirst :=
                  close_new_exactFst scope storedFirst storedLabel lowerWf
                    upperWf nonempty closing behavior
                    (arguments storedFirst) payload'
                _ = arguments.extend behavior.argument first := by
                  rw [← parts.1]
                  rfl
      | succ oldPackage =>
          let old := olderMember member
          have slotEq := Scope.lookupMember_irrel
            (TermTranslation.compileBinder scope sourceWf).extended member
            old.old.there
          have translated :
              (translatePath
                  (TermTranslation.compileBinder scope sourceWf).extended
                  (Fragment.PathTy.exactFst member)).expression =
                (translatePath
                  (TermTranslation.compileBinder scope sourceWf).extended
                  (Fragment.PathTy.exactFst old.old.there)).expression := by
            exact congrArg (fun slot => slot.payloadPath.expression) slotEq
          have sameClosed := congrArg
            (extendClosing closing
              (TermTranslation.compileBinder scope sourceWf).plan behavior).closeExp
            translated
          have renamed := congrArg
            (extendClosing closing
              (TermTranslation.compileBinder scope sourceWf).plan behavior).closeExp
            (translatePath_old_exactFst_expression scope sourceWf old.old)
          have closedOld :
              (extendClosing closing
                  (TermTranslation.compileBinder scope sourceWf).plan
                  behavior).closeExp
                (translatePath
                  (TermTranslation.compileBinder scope sourceWf).extended
                  (Fragment.PathTy.exactFst member)).expression =
                arguments old.oldFirst := by
            simpa only [pathReferentIndex_exactFst] using
              sameClosed.trans
                (renamed.trans
                  ((close_old_expression closing _ behavior
                    (translatePath scope
                      (Fragment.PathTy.exactFst old.old)).expression).trans
                    (older (Fragment.PathTy.exactFst old.old))))
          exact closedOld.trans (by
            simpa only [pathReferentIndex_exactFst,
              ClosedArguments.extend, Fin.cases_succ] using
              congrArg (arguments.extend behavior.argument) old.firstEq)

/-! ## External coherence for a compiled store environment -/

/-- The closed target argument advertised by each lexical slot in a compiled
store environment. -/
noncomputable def storeArguments
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : OperationalEnvironment.ClosingEnv sig []}
    (store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing) : ClosedArguments lexical :=
  fun index => (store.lookup index).slot.behavior.argument

/-- External target-path invariant for `StoreEnvironment`.  Keeping this
predicate separate prevents native source-cell provenance from being
conflated with the adapted target behavior of lexical slots. -/
noncomputable def StorePathCoherence
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : OperationalEnvironment.ClosingEnv sig []}
    (store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing) : Prop :=
  ClosedPathAgreement scope closing (storeArguments store)

namespace StorePathCoherence

/-- The variable specialization used by a source path step. -/
theorem close_var
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : OperationalEnvironment.ClosingEnv sig []}
    {store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing}
    (coherent : StorePathCoherence store) (index : Fin lexical) :
    closing.closeExp
        (translatePath scope
          (Fragment.PathTy.var
            (Γ := sourceContext) (x := index))).expression =
      (store.lookup index).slot.behavior.argument :=
  coherent (Fragment.PathTy.var (Γ := sourceContext) (x := index))

/-- The exact-first specialization used by a source projection step. -/
theorem close_exactFst
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : OperationalEnvironment.ClosingEnv sig []}
    {store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing}
    (coherent : StorePathCoherence store)
    {package first : Fin lexical} {label : LambdaPFC.Name}
    {lower upper : LambdaPFC.Ty lexical}
    (member : Fragment.BoundMember sourceContext package label lower upper
      first) :
    closing.closeExp
        (translatePath scope
          (Fragment.PathTy.exactFst member)).expression =
      (store.lookup first).slot.behavior.argument :=
  coherent (Fragment.PathTy.exactFst member)

/-- The empty compiled store has no supported source paths. -/
theorem empty : StorePathCoherence StoreEnvironment.initial := by
  intro path sourceType typing
  nomatch typing

/-- A native-only allocation changes neither the lexical target scope nor
the target behavior of any existing slot. -/
theorem nativeWeaken
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : OperationalEnvironment.ClosingEnv sig []}
    {older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing}
    (coherent : StorePathCoherence older)
    (runtimeValue : LambdaPFC.Tm current)
    (runtimeReady : runtimeValue.IsValue) :
    StorePathCoherence
      (StoreEnvironment.nativeWeaken older runtimeValue runtimeReady) := by
  exact coherent

/-- Generic external builder for any of the three lexical extension
constructors (`extend`, `alias`, or `bindLocation`).  Their lookup equations
are definitional; the only new semantic premises are `RawSlot` and, for an
exact member binder, `NewPayloadAgreement`. -/
theorem extend
    {n current nextCurrent : Nat}
    {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : OperationalEnvironment.ClosingEnv sig []}
    {older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing}
    (coherent : StorePathCoherence older)
    {sourceType : LambdaPFC.Ty n}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (behavior : EliminationView
      ((TermTranslation.compileBinder scope sourceWf).plan.subst
        closing.substitution))
    (raw : RawSlot behavior)
    (payload : NewPayloadAgreement scope sourceWf closing behavior
      (storeArguments older))
    {nextStore : LambdaPFC.Store nextCurrent}
    {nextValuation : SourceValuation (n + 1) nextCurrent}
    (newStore : StoreEnvironment (sourceContext.snoc sourceType) nextStore
      nextValuation
      ((TermTranslation.compileBinder scope sourceWf).plan.context
        targetContext)
      (TermTranslation.compileBinder scope sourceWf).extended
      (extendClosing closing
        (TermTranslation.compileBinder scope sourceWf).plan behavior))
    (newest : (newStore.lookup 0).slot.behavior.argument =
      behavior.argument)
    (olderSlots : forall index : Fin n,
      (newStore.lookup index.succ).slot.behavior.argument =
        (older.lookup index).slot.behavior.argument) :
    StorePathCoherence newStore := by
  unfold StorePathCoherence at coherent ⊢
  have extended : ClosedPathAgreement
      (TermTranslation.compileBinder scope sourceWf).extended
      (extendClosing closing
        (TermTranslation.compileBinder scope sourceWf).plan behavior)
      ((storeArguments older).extend behavior.argument) :=
    ClosedPathAgreement.extend coherent sourceWf behavior raw payload
  have argumentsEq : storeArguments newStore =
      (storeArguments older).extend behavior.argument := by
    funext index
    cases index using Fin.cases with
    | zero => exact newest
    | succ olderIndex => exact olderSlots olderIndex
  rw [argumentsEq]
  intro path sourceType typing
  exact extended typing

end StorePathCoherence

end OperationalPathCoherence
end LambdaPToFCo
