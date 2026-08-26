import LambdaPToFCo.OperationalStateImage

/-!
# Source progress exposed by the operational machine image

The executable machine image is already strong enough to prove progress of
the source CK state.  This proof uses only the retained source syntax,
valuation-indexed store environment, and exact-core admissibility evidence;
the target focus and target reduction history play no role.

The only nontrivial head case is application.  `FunctionPathSpine` restricts
the operator to a variable introduced at its precise arrow type, surrounded
only by structural arrow coercions.  The helper below follows that variable
back through lexical extensions and hidden native allocations and applies the
`FunctionCell` stored at the corresponding physical location.
-/

namespace LambdaPToFCo
namespace OperationalSourceProgress

open OperationalCode
open OperationalStoreEnvironment
open OperationalAdmissibility
open OperationalApplicationSourceEndpoint
open OperationalFunctionPathSpine
open OperationalStateImage

namespace Fragment.Wf

/-- If weakening a well-formed fragment type has an arrow head, the original
type was already one of the fragment's nondependent arrows. -/
theorem arrow_of_weaken_eq
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceType : LambdaPFC.Ty lexical}
    (wf : Fragment.Wf sourceContext sourceType)
    {domain codomain : LambdaPFC.Ty (lexical + 1)}
    (type_eq : sourceType.weaken = .Fun domain codomain.weaken) :
    Exists fun sourceDomain : LambdaPFC.Ty lexical =>
      Exists fun sourceCodomain : LambdaPFC.Ty lexical =>
        sourceType = .Fun sourceDomain sourceCodomain.weaken := by
  cases wf with
  | top => cases type_eq
  | singleton _ => cases type_eq
  | selection _ _ => cases type_eq
  | memberPackage _ _ _ => cases type_eq
  | arrow _ _ => exact ⟨_, _, rfl⟩

end Fragment.Wf

namespace StoreEnvironment

/-- A variable whose current context type has an arrow head denotes a native
abstraction cell.

The proof mirrors the store-environment spine.  Later allocations weaken the
native binding; lexical extensions either use their own `FunctionCell` at the
newest variable or recurse to the older environment.  `Scope.Coherent`
supplies well-formedness of an older lookup, which is what lets us invert an
arrow seen only after weakening. -/
theorem lookup_function
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : SystemFCo.Sig} {targetContext : SystemFCo.Ctx sig}
    {scope : StaticTranslation.Scope sourceContext targetContext}
    {closing : OperationalEnvironment.ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing) :
    {index : Fin lexical} ->
    {domain : LambdaPFC.Ty lexical} ->
    {codomain : LambdaPFC.Ty lexical} ->
    sourceContext.lookup index = .Fun domain codomain.weaken ->
    Exists fun runtimeDomain : LambdaPFC.Ty current =>
      Exists fun runtimeBody : LambdaPFC.Tm (current + 1) =>
        LambdaPFC.Store.Binds sourceStore (valuation index)
          (.abs runtimeDomain runtimeBody) := by
  induction environment with
  | empty => intro index; exact Fin.elim0 index
  | nativeWeaken older runtimeValue runtimeReady ih =>
      intro index domain codomain type_eq
      rcases ih type_eq with ⟨runtimeDomain, runtimeBody, binds⟩
      exact ⟨runtimeDomain.weaken,
        runtimeBody.rename LambdaPFC.FinFun.weaken.ext, .there binds⟩
  | extend older typing native nativeValuation nativeAdmissible nativeEvidence
      nativeEnvironment nativeReady runtimeReady runtime_eq memberCell
      functionCell behavior normalizes ih =>
      intro index domain codomain type_eq
      cases index using Fin.cases with
      | zero =>
        rcases OperationalSourceProgress.Fragment.Wf.arrow_of_weaken_eq
            typing.typeWf type_eq with
          ⟨sourceDomain, sourceCodomain, source_eq⟩
        exact functionCell source_eq
      | succ olderIndex =>
        let olderWf := older.coherent.lookup_wf olderIndex
        rcases OperationalSourceProgress.Fragment.Wf.arrow_of_weaken_eq
            olderWf type_eq with
          ⟨sourceDomain, sourceCodomain, source_eq⟩
        rcases ih source_eq with ⟨runtimeDomain, runtimeBody, binds⟩
        exact ⟨runtimeDomain.weaken,
          runtimeBody.rename LambdaPFC.FinFun.weaken.ext, .there binds⟩
  | alias older typing memberCell functionCell behavior normalizes ih =>
      intro index domain codomain type_eq
      cases index using Fin.cases with
      | zero =>
        rcases OperationalSourceProgress.Fragment.Wf.arrow_of_weaken_eq
            typing.typeWf type_eq with
          ⟨sourceDomain, sourceCodomain, source_eq⟩
        exact functionCell source_eq
      | succ olderIndex =>
        let olderWf := older.coherent.lookup_wf olderIndex
        rcases OperationalSourceProgress.Fragment.Wf.arrow_of_weaken_eq
            olderWf type_eq with
          ⟨sourceDomain, sourceCodomain, source_eq⟩
        exact ih source_eq
  | bindLocation older sourceWf location binds compiled nativeEnvironment
      memberCell functionCell behavior ih =>
      intro index domain codomain type_eq
      cases index using Fin.cases with
      | zero =>
        rcases OperationalSourceProgress.Fragment.Wf.arrow_of_weaken_eq
            sourceWf type_eq with
          ⟨sourceDomain, sourceCodomain, source_eq⟩
        exact functionCell source_eq
      | succ olderIndex =>
        let olderWf := older.coherent.lookup_wf olderIndex
        rcases OperationalSourceProgress.Fragment.Wf.arrow_of_weaken_eq
            olderWf type_eq with
          ⟨sourceDomain, sourceCodomain, source_eq⟩
        exact ih source_eq

end StoreEnvironment

/-- A precisely arrow-typed fragment path can only be a variable, and the
corresponding variable lookup has an abstraction head. -/
theorem path_function
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : SystemFCo.Sig} {targetContext : SystemFCo.Ctx sig}
    {scope : StaticTranslation.Scope sourceContext targetContext}
    {closing : OperationalEnvironment.ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    {path : LambdaPFC.Path lexical} {sourceType : LambdaPFC.Ty lexical}
    (pathTyping : Fragment.PathTy sourceContext path sourceType)
    {domain codomain : LambdaPFC.Ty lexical}
    (type_eq : sourceType = .Fun domain codomain.weaken) :
    Exists fun runtimeDomain : LambdaPFC.Ty current =>
      Exists fun runtimeBody : LambdaPFC.Tm (current + 1) =>
        LambdaPFC.Store.Binds sourceStore
          (valuation (pathReferentIndex pathTyping))
          (.abs runtimeDomain runtimeBody) := by
  cases pathTyping with
  | var =>
      exact OperationalSourceProgress.StoreEnvironment.lookup_function
        environment type_eq
  | exactFst _ => cases type_eq

namespace FunctionPathSpine

/-- Source resolution selected by the typing index carried by a function
path spine. -/
theorem source_resolution
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : SystemFCo.Sig} {targetContext : SystemFCo.Ctx sig}
    {scope : StaticTranslation.Scope sourceContext targetContext}
    {closing : OperationalEnvironment.ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    {path : LambdaPFC.Path lexical}
    {domain codomain : LambdaPFC.Ty lexical}
    {typing : Fragment.HasType sourceContext (.path path)
      (.Fun domain codomain.weaken)}
    (_spine : FunctionPathSpine typing) :
    LambdaPFC.Path.Resolve (path.rename valuation) sourceStore
      (.loc (valuation (typedPathReferent typing))) :=
  resolveTypedPath environment typing

/-- The exact-core function-path spine resolves to an abstraction at its
static referent.  Outer arrow coercions preserve that referent. -/
theorem source_function
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : SystemFCo.Sig} {targetContext : SystemFCo.Ctx sig}
    {scope : StaticTranslation.Scope sourceContext targetContext}
    {closing : OperationalEnvironment.ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    {path : LambdaPFC.Path lexical}
    {domain codomain : LambdaPFC.Ty lexical}
    {typing : Fragment.HasType sourceContext (.path path)
      (.Fun domain codomain.weaken)}
    (spine : FunctionPathSpine typing) :
    Exists fun runtimeDomain : LambdaPFC.Ty current =>
      Exists fun runtimeBody : LambdaPFC.Tm (current + 1) =>
        LambdaPFC.Store.Binds sourceStore
          (valuation (typedPathReferent typing))
          (.abs runtimeDomain runtimeBody) := by
  induction spine with
  | widen pathTyping domainWf codomainWf domainShape =>
      rw [typedPathReferent_sub, typedPathReferent_path]
      exact OperationalSourceProgress.path_function environment pathTyping rfl
  | sub inner coercion ih =>
      rw [typedPathReferent_sub]
      exact ih

end FunctionPathSpine

/-- Resolution selected by the typing index of an admissible path. -/
theorem admissible_path_resolution
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : SystemFCo.Sig} {targetContext : SystemFCo.Ctx sig}
    {scope : StaticTranslation.Scope sourceContext targetContext}
    {closing : OperationalEnvironment.ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    {path : LambdaPFC.Path lexical} {sourceType : LambdaPFC.Ty lexical}
    {typing : Fragment.HasType sourceContext (.path path) sourceType}
    (_admissible : OperationallyAdmissible typing) :
    LambdaPFC.Path.Resolve (path.rename valuation) sourceStore
      (.loc (valuation (typedPathReferent typing))) :=
  resolveTypedPath environment typing

/-- A direct valuation closure of admissible source code makes CK progress. -/
theorem direct_progress
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : SystemFCo.Sig} {targetContext : SystemFCo.Ctx sig}
    {scope : StaticTranslation.Scope sourceContext targetContext}
    {closing : OperationalEnvironment.ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    {sourceTerm : LambdaPFC.Tm lexical}
    {sourceType : LambdaPFC.Ty lexical}
    {typing : Fragment.HasType sourceContext sourceTerm sourceType}
    (admissible : OperationallyAdmissible typing)
    {runtimeTerm : LambdaPFC.Tm current}
    (runtime_eq : runtimeTerm = sourceTerm.rename valuation)
    (runtimeCont : LambdaPFC.Tm.Cont current) :
    LambdaPFC.State.Progress
      (LambdaPFC.State.mk sourceStore runtimeCont runtimeTerm) := by
  induction admissible generalizing runtimeTerm runtimeCont with
  | path pathTyping =>
      rw [runtime_eq]
      cases pathTyping with
      | var => exact LambdaPFC.State.Progress.path_var
      | exactFst member =>
          apply LambdaPFC.State.Progress.step
          exact .path
            (environment.resolvePath (.exactFst member))
            (by intro isVariable; cases isVariable)
  | functionPath spine =>
      rw [runtime_eq]
      cases spine.pathIsVar
      exact LambdaPFC.State.Progress.path_var
  | function spine bodyAdmissible ih =>
      rw [runtime_eq]
      exact LambdaPFC.State.Progress.value .abs
  | package spine =>
      rw [runtime_eq]
      exact LambdaPFC.State.Progress.value .pair
  | app function functionSpine argument resultShape functionIH argumentIH =>
      rw [runtime_eq]
      let functionResolution :=
        OperationalSourceProgress.FunctionPathSpine.source_resolution
          environment functionSpine
      let argumentResolution :=
        admissible_path_resolution environment argument
      rcases OperationalSourceProgress.FunctionPathSpine.source_function
          environment functionSpine with
        ⟨runtimeDomain, runtimeBody, functionBinds⟩
      exact LambdaPFC.State.Progress.step
        (.app functionResolution argumentResolution functionBinds)
  | «let» bound boundPolicy body resultShape boundIH bodyIH =>
      rw [runtime_eq]
      exact LambdaPFC.State.Progress.step .let_push
  | neutralSub neutral inner subtype targetShape ih =>
      exact ih environment runtime_eq runtimeCont

namespace CurrentCodeEnvironment

/-- Progress depends only on the current source-code form, independently of
the target focus occupying the zipper hole. -/
theorem sourceProgress
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeTerm : LambdaPFC.Tm current} {focus : SystemFCo.Exp []}
    (code : CurrentCodeEnvironment sourceStore runtimeTerm focus)
    (runtimeCont : LambdaPFC.Tm.Cont current) :
    LambdaPFC.State.Progress
      (LambdaPFC.State.mk sourceStore runtimeCont runtimeTerm) := by
  cases code with
  | mk origin form =>
      cases form with
      | direct runtime_eq =>
          exact direct_progress origin.environment origin.admissible runtime_eq
            runtimeCont
      | resolvedPath _ _ _ =>
          exact LambdaPFC.State.Progress.path_var

end CurrentCodeEnvironment

/-- Every complete machine image entails progress of its source CK state.

Resolved paths are runtime variables and therefore final or returning.
Nothing in the statement assumes target progress or target safety. -/
theorem StateImage.sourceProgress
    {current : Nat} {state : LambdaPFC.State current}
    (image : StateImage state) : state.Progress := by
  exact OperationalSourceProgress.CurrentCodeEnvironment.sourceProgress
    image.current state.cont

end OperationalSourceProgress
end LambdaPToFCo
