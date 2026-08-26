import LambdaPToFCo.OperationalBindingView
import LambdaPToFCo.OperationalClosedFrames
import LambdaPToFCo.OperationalAdmissibilityCore

/-!
# Valuation-indexed compiled source-store environments

The native store scope and the lexical scope of retained source code need not
coincide.  This module records that distinction directly: a
`StoreEnvironment` is indexed by an original fragment context and a source
valuation into the current native store.  Allocation extends the original
context and the valuation together; it never invents a typing derivation for
the renamed run-time value.

Each allocated cell retains its original derivation, its own static target
compilation and closing environment, and an `EliminationView` describing the
target behavior of its binder.  The view may leave an explicit administrative
resumption, so this foundation does not assume that elimination lands
directly at a substituted body.  No resumption/simulation theorem is claimed
here.
-/

namespace LambdaPToFCo
namespace OperationalStoreEnvironment

open SystemFCo
open StaticTranslation
open OperationalCode
open OperationalBindingView
open OperationalValueEvidence
open OperationalApplicationSpine
open OperationalAdmissibility

/-! ## Closing with behavioral slot substitutions -/

/-- Extend a closing environment by the slot substitution exposed by a
behavioral binding view.  Unlike `ClosingEnv.extend`, this does not require a
literal `Instantiation`. -/
def extendClosing
    (environment : OperationalEnvironment.ClosingEnv sig target)
    (plan : Interface.BinderPlan sig)
    (view : EliminationView
      (plan.subst environment.substitution)) :
    OperationalEnvironment.ClosingEnv plan.scope target :=
  ⟨(plan.scopeSubst environment.substitution).comp view.substitution⟩

/-- Closing after a behavioral extension is substitution of the exposed
slots followed by the older closing environment. -/
theorem closeExp_extendClosing
    (environment : OperationalEnvironment.ClosingEnv sig target)
    (plan : Interface.BinderPlan sig)
    (view : EliminationView
      (plan.subst environment.substitution))
    (body : Exp plan.scope) :
    (extendClosing environment plan view).closeExp body =
      view.instantiate (environment.closeBody plan body) := by
  exact Exp.subst_comp body (plan.scopeSubst environment.substitution)
    view.substitution |>.symm

/-! ## Lexical slots and native allocation provenance -/

/-- Minimal interface installed for one lexical source variable.

Unlike `CompiledSlot`, this does not claim that the interface arose from a
closed source computation.  Beta and return bind an already allocated
location and therefore have a well-formed source type plus adapted target
behavior, but no same-context source path whose compilation normalized to
that behavior. -/
structure LexicalSlot : Type where
  arity : Nat
  context : LambdaPFC.Ctx arity
  sourceType : LambdaPFC.Ty arity
  sourceWf : Fragment.Wf context sourceType
  targetSig : Sig
  targetContext : Ctx targetSig
  scope : Scope context targetContext
  environment : OperationalEnvironment.ClosingEnv targetSig []
  behavior : EliminationView
    ((TermTranslation.compileBinder scope sourceWf).plan.subst
      environment.substitution)

namespace LexicalSlot

/-- The closed target argument exposed by this lexical interface. -/
noncomputable def closedArgument (slot : LexicalSlot) : Exp [] :=
  slot.behavior.argument

end LexicalSlot

/-- Compilation data owned by one lexical source slot.  This record does not
claim that its source term is the native value at any store location: that
extra fact belongs only to genuinely allocated cells.  In particular, an
alias slot can compile a source path while reusing a different cell's native
provenance. -/
structure CompiledSlot : Type where
  original : TypedCode
  compilation : TypedCode.Compilation original
  environment : OperationalEnvironment.ClosingEnv
    compilation.targetSig []
  behavior : EliminationView
    ((TermTranslation.compileBinder compilation.scope
      original.typing.typeWf).plan.subst environment.substitution)
  normalizes : Exp.Steps
    (environment.closeExp compilation.expression) behavior.argument

namespace CompiledSlot

/-- Forget computation provenance while retaining the lexical binder
interface. -/
noncomputable def lexical (slot : CompiledSlot) : LexicalSlot where
  arity := slot.original.arity
  context := slot.original.context
  sourceType := slot.original.resultType
  sourceWf := slot.original.typing.typeWf
  targetSig := slot.compilation.targetSig
  targetContext := slot.compilation.targetContext
  scope := slot.compilation.scope
  environment := slot.environment
  behavior := slot.behavior

/-- The closed target argument stored in this lexical slot. -/
noncomputable def closedArgument (slot : CompiledSlot) : Exp [] :=
  slot.behavior.argument

/-- Closing preserves the retained normalization to the slot's behavioral
argument. -/
theorem close_normalizes (slot : CompiledSlot) :
    Exp.Steps
      (slot.compilation.close slot.environment)
      slot.closedArgument :=
  slot.normalizes

end CompiledSlot

/-- Native allocation provenance paired with the lexical target slot that
was installed when the value was allocated.

The two source origins are intentionally independent.  In particular, after
CK application the native value is a valuation instance of the function
body, while the lexical slot still owns the original application derivation
and its residual target adaptations.  The native closed value and adapted
slot behavior are therefore not equated here; canonical-head consumers carry
that compatibility only in the cases where they need it. -/
structure CompiledBinding {current : Nat}
    (runtimeValue : LambdaPFC.Tm current) : Type where
  /-- The adapted source/target interface installed at allocation. -/
  slot : CompiledSlot
  /-- Original source code whose valuation closure is the native value. -/
  native : TypedCode
  nativeValuation : SourceValuation native.arity current
  nativeAdmissible : OperationallyAdmissible native.typing
  nativeEvidence : ApplicationValueEvidence native.typing
  nativeTargetSig : Sig
  nativeTargetContext : Ctx nativeTargetSig
  nativeScope : Scope native.context nativeTargetContext
  nativeClosing : OperationalEnvironment.ClosingEnv nativeTargetSig []
  nativeReady : nativeEvidence.ClosedReady nativeScope nativeClosing
  runtime_eq : runtimeValue = native.term.rename nativeValuation

namespace CompiledBinding

/-- The closed target argument represented by this allocated cell. -/
noncomputable def closedArgument (binding : CompiledBinding runtimeValue) :
    Exp [] :=
  binding.slot.closedArgument

/-- The retained original elaboration reduces to the behavioral argument
after both are closed with this cell's own target environment. -/
theorem close_normalizes (binding : CompiledBinding runtimeValue) :
    Exp.Steps
      (binding.slot.compilation.close binding.slot.environment)
      binding.closedArgument :=
  binding.slot.close_normalizes

/-- Existing native locations and their original code closures survive one
later allocation.  Their target compilation and behavior do not change. -/
noncomputable def weaken (binding : CompiledBinding runtimeValue) :
    CompiledBinding runtimeValue.weaken where
  slot := binding.slot
  native := binding.native
  nativeValuation := binding.nativeValuation.weaken
  nativeAdmissible := binding.nativeAdmissible
  nativeEvidence := binding.nativeEvidence
  nativeTargetSig := binding.nativeTargetSig
  nativeTargetContext := binding.nativeTargetContext
  nativeScope := binding.nativeScope
  nativeClosing := binding.nativeClosing
  nativeReady := binding.nativeReady
  runtime_eq := by
    calc
      runtimeValue.weaken =
          (binding.native.term.rename binding.nativeValuation).weaken :=
        congrArg LambdaPFC.Tm.weaken binding.runtime_eq
      _ = binding.native.term.rename binding.nativeValuation.weaken :=
        SourceValuation.rename_weaken binding.native.term
          binding.nativeValuation

end CompiledBinding

/-! ## Static referents of supported source paths -/

/-- Store index denoted by a statically supported fragment path.  Variables
refer to themselves; the only supported projection, an exact first
projection, refers to the member package's retained `first` index. -/
def pathReferentIndex :
    {n : Nat} -> {context : LambdaPFC.Ctx n} ->
    {path : LambdaPFC.Path n} -> {sourceType : LambdaPFC.Ty n} ->
    Fragment.PathTy context path sourceType -> Fin n
| _, _, _, _, @Fragment.PathTy.var _ _ index => index
| _, _, _, _, @Fragment.PathTy.exactFst _ _ _ first _ _ _ _ => first

@[simp] theorem pathReferentIndex_var
    {context : LambdaPFC.Ctx n} (index : Fin n) :
    pathReferentIndex
        (Fragment.PathTy.var (Γ := context) (x := index)) = index :=
  rfl

@[simp] theorem pathReferentIndex_exactFst
    {context : LambdaPFC.Ctx n} {package first : Fin n}
    {label : LambdaPFC.Name} {lower upper : LambdaPFC.Ty n}
    (member : Fragment.BoundMember context package label lower upper first) :
    pathReferentIndex (Fragment.PathTy.exactFst member) = first :=
  rfl

/-- Peel source subsumption from a typed fragment path and return its static
store referent.  Dependent indexing rules out every non-path typing
constructor. -/
def typedPathReferent :
    {n : Nat} -> {context : LambdaPFC.Ctx n} ->
    {path : LambdaPFC.Path n} -> {sourceType : LambdaPFC.Ty n} ->
    (typing : Fragment.HasType context (.path path) sourceType) -> Fin n
| _, _, _, _, .path pathTyping => pathReferentIndex pathTyping
| _, _, _, _, .sub termTyping _ => typedPathReferent termTyping

@[simp] theorem typedPathReferent_path
    (pathTyping : Fragment.PathTy context path sourceType) :
    typedPathReferent (Fragment.HasType.path pathTyping) =
      pathReferentIndex pathTyping :=
  by simp only [typedPathReferent]

@[simp] theorem typedPathReferent_sub
    (typing : Fragment.HasType context (.path path) sourceType)
    (subtype : Fragment.Sub context sourceType targetType) :
    typedPathReferent (Fragment.HasType.sub typing subtype) =
      typedPathReferent typing :=
  by simp only [typedPathReferent]

/-! ## Canonical native heads for member-typed lexical slots -/

/-- The minimal native provenance needed to resolve an exact first
projection.  If the new lexical source type is a member package, its chosen
store location contains a type-package pair with the same static first index
and label.  Non-member source types make the implication vacuous.

This is deliberately operational shape, not semantic realization. -/
def MemberCell
    (sourceType : LambdaPFC.Ty lexical)
    (sourceStore : LambdaPFC.Store current)
    (valuation : SourceValuation lexical current)
    (location : Fin current) : Prop :=
  {first : Fin lexical} -> {label : LambdaPFC.Name} ->
  {lower upper : LambdaPFC.Ty lexical} ->
  sourceType = Fragment.memberPackageTy first label lower upper ->
    Exists fun witness : LambdaPFC.Ty current =>
      LambdaPFC.Store.Binds sourceStore location
        (.pair (valuation first) label (.type witness))

namespace MemberCell

/-- Ordinary fragment shapes cannot trigger the member-cell obligation. -/
theorem ofNotMember
    (notMember : StaticTranslation.NotMember sourceType) :
    MemberCell sourceType sourceStore valuation location := by
  intro first label lower upper typeEq
  exact (notMember
    { first := first
      label := label
      lower := lower
      upper := upper
      equality := typeEq }).elim

/-- Exact package allocation supplies canonical member-cell provenance
directly from syntactic valuation closure. -/
theorem allocateTypePackage
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {first : Fin lexical} {label : LambdaPFC.Name}
    {witness : LambdaPFC.Ty lexical}
    {runtimeValue : LambdaPFC.Tm current}
    (runtimeReady : runtimeValue.IsValue)
    (runtime_eq : runtimeValue =
      (LambdaPFC.Tm.pair first label (.type witness)).rename valuation) :
    MemberCell (Fragment.exactPackageTy first label witness)
      (.val sourceStore runtimeValue runtimeReady) valuation.weaken 0 := by
  cases runtime_eq
  intro otherFirst otherLabel lower upper typeEq
  have parts := Fragment.memberPackageTy_injective typeEq
  cases parts.1
  cases parts.2.1
  refine ⟨(witness.rename valuation).weaken, ?_⟩
  exact .here

/-- Member-head provenance survives a later native allocation. -/
theorem weaken
    {lexical current : Nat}
    {sourceType : LambdaPFC.Ty lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {location : Fin current}
    (cell : MemberCell sourceType sourceStore valuation location)
    (newValue : LambdaPFC.Tm current)
    (newReady : newValue.IsValue) :
    MemberCell sourceType
      (@LambdaPFC.Store.val current sourceStore newValue newReady)
      valuation.weaken location.succ := by
  intro first label lower upper typeEq
  rcases cell typeEq with ⟨witness, binds⟩
  exact ⟨witness.weaken, .there binds⟩

end MemberCell

/-- The minimal native provenance needed by CK function application.  If a
lexical slot is advertised at a function type, its chosen store location has
an abstraction head.  Target arrow evidence is intentionally separate. -/
def FunctionCell
    (sourceType : LambdaPFC.Ty lexical)
    (sourceStore : LambdaPFC.Store current)
    (_valuation : SourceValuation lexical current)
    (location : Fin current) : Prop :=
  {domain codomain : LambdaPFC.Ty lexical} ->
  sourceType = .Fun domain codomain.weaken ->
    Exists fun runtimeDomain : LambdaPFC.Ty current =>
      Exists fun runtimeBody : LambdaPFC.Tm (current + 1) =>
        LambdaPFC.Store.Binds sourceStore location
          (.abs runtimeDomain runtimeBody)

namespace FunctionCell

/-- Direct abstraction allocation supplies the canonical function head from
syntactic valuation closure. -/
theorem allocateAbs
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {domain codomain : LambdaPFC.Ty lexical}
    {body : LambdaPFC.Tm (lexical + 1)}
    {runtimeValue : LambdaPFC.Tm current}
    (runtimeReady : runtimeValue.IsValue)
    (runtime_eq : runtimeValue =
      (LambdaPFC.Tm.abs domain body).rename valuation) :
    FunctionCell (.Fun domain codomain.weaken)
      (.val sourceStore runtimeValue runtimeReady) valuation.weaken 0 := by
  cases runtime_eq
  intro _ _ _
  exact ⟨(domain.rename valuation).weaken,
    (body.rename valuation.ext).rename LambdaPFC.FinFun.weaken.ext,
    .here⟩

/-- Function-head provenance survives a later native allocation. -/
theorem weaken
    {lexical current : Nat}
    {sourceType : LambdaPFC.Ty lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {location : Fin current}
    (cell : FunctionCell sourceType sourceStore valuation location)
    (newValue : LambdaPFC.Tm current)
    (newReady : newValue.IsValue) :
    FunctionCell sourceType
      (@LambdaPFC.Store.val current sourceStore newValue newReady)
      valuation.weaken location.succ := by
  intro domain codomain typeEq
  rcases cell typeEq with ⟨runtimeDomain, runtimeBody, binds⟩
  exact ⟨runtimeDomain.weaken,
    runtimeBody.rename LambdaPFC.FinFun.weaken.ext, .there binds⟩

end FunctionCell

/-! ## Allocation spine indexed by lexical context and valuation -/

/-- A compiled lexical view of a native source store.

The `nativeWeaken` constructor records an allocation hidden from this
particular lexical view: it grows only the native store and weakens the
valuation, leaving the source context, target scope, and closing substitution
unchanged.  This is what lets suspended frames and saved function
environments survive allocations performed elsewhere.

The `extend` constructor keeps the lexical computation used for the new
source/target interface separate from the original code closure of the
native value.  The `alias` constructor extends the lexical interfaces but
maps the new source variable to an existing store location.  In both cases
target behavior is abstracted by `EliminationView`; no literal package
instantiation is assumed. -/
inductive StoreEnvironment :
    {lexical : Nat} -> (sourceContext : LambdaPFC.Ctx lexical) ->
    {current : Nat} -> (sourceStore : LambdaPFC.Store current) ->
    (valuation : SourceValuation lexical current) ->
    {sig : Sig} -> (targetContext : Ctx sig) ->
    (scope : Scope sourceContext targetContext) ->
    OperationalEnvironment.ClosingEnv sig [] -> Type where
| empty : StoreEnvironment LambdaPFC.Ctx.nil LambdaPFC.Store.empty
    SourceValuation.identity SystemFCo.Ctx.empty Scope.empty
    OperationalEnvironment.ClosingEnv.identity
| nativeWeaken
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closingEnv : OperationalEnvironment.ClosingEnv sig []}
    (older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closingEnv)
    (runtimeValue : LambdaPFC.Tm current)
    (runtimeReady : runtimeValue.IsValue) :
    StoreEnvironment sourceContext
      (.val sourceStore runtimeValue runtimeReady) valuation.weaken
      targetContext scope closingEnv
| extend
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {olderClosing : OperationalEnvironment.ClosingEnv sig []}
    (older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope olderClosing)
    {sourceTerm : LambdaPFC.Tm lexical}
    {sourceType : LambdaPFC.Ty lexical}
    (typing : Fragment.HasType sourceContext sourceTerm sourceType)
    /- Source-code closure of the native value.  This need not be the
    lexical computation described by `typing` (notably after CK beta). -/
    (native : TypedCode)
    (nativeValuation : SourceValuation native.arity current)
    (nativeAdmissible : OperationallyAdmissible native.typing)
    (nativeEvidence : ApplicationValueEvidence native.typing)
    {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
    {nativeScope : Scope native.context nativeTargetContext}
    {nativeClosing : OperationalEnvironment.ClosingEnv nativeSig []}
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
      behavior.argument) :
    StoreEnvironment
      (sourceContext.snoc sourceType)
      (.val sourceStore runtimeValue runtimeReady)
      valuation.ext
      ((TermTranslation.compileBinder scope typing.typeWf).plan.context
        targetContext)
      (TermTranslation.compileBinder scope typing.typeWf).extended
      (extendClosing olderClosing
        (TermTranslation.compileBinder scope typing.typeWf).plan behavior)
| alias
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {olderClosing : OperationalEnvironment.ClosingEnv sig []}
    (older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope olderClosing)
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
      behavior.argument) :
    StoreEnvironment
      (sourceContext.snoc sourceType)
      sourceStore
      (valuation.bind (valuation (typedPathReferent typing)))
      ((TermTranslation.compileBinder scope typing.typeWf).plan.context
        targetContext)
      (TermTranslation.compileBinder scope typing.typeWf).extended
      (extendClosing olderClosing
        (TermTranslation.compileBinder scope typing.typeWf).plan behavior)
| bindLocation
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {olderClosing : OperationalEnvironment.ClosingEnv sig []}
    (older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope olderClosing)
    {sourceType : LambdaPFC.Ty lexical}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (location : Fin current)
    {runtimeValue : LambdaPFC.Tm current}
    (binds : LambdaPFC.Store.Binds sourceStore location runtimeValue)
    (compiled : CompiledBinding runtimeValue)
    {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
    {nativeScope : Scope compiled.native.context nativeTargetContext}
    {nativeClosing : OperationalEnvironment.ClosingEnv nativeSig []}
    (nativeEnvironment : StoreEnvironment compiled.native.context sourceStore
      compiled.nativeValuation nativeTargetContext nativeScope nativeClosing)
    (memberCell : MemberCell sourceType sourceStore valuation location)
    (functionCell : FunctionCell sourceType sourceStore valuation location)
    (behavior : EliminationView
      ((TermTranslation.compileBinder scope sourceWf).plan.subst
        olderClosing.substitution)) :
    StoreEnvironment
      (sourceContext.snoc sourceType)
      sourceStore
      (valuation.bind location)
      ((TermTranslation.compileBinder scope sourceWf).plan.context
        targetContext)
      (TermTranslation.compileBinder scope sourceWf).extended
      (extendClosing olderClosing
        (TermTranslation.compileBinder scope sourceWf).plan behavior)

namespace StoreEnvironment

/-- Canonical empty compiled environment. -/
def initial : StoreEnvironment LambdaPFC.Ctx.nil LambdaPFC.Store.empty
    SourceValuation.identity SystemFCo.Ctx.empty Scope.empty
    OperationalEnvironment.ClosingEnv.identity :=
  .empty

/-- Coherence is inherited from the empty scope and preserved by every
derivation-selected binder extension. -/
noncomputable def coherent :
    {lexical : Nat} -> {sourceContext : LambdaPFC.Ctx lexical} ->
    {current : Nat} -> {sourceStore : LambdaPFC.Store current} ->
    {valuation : SourceValuation lexical current} ->
    {sig : Sig} -> {targetContext : Ctx sig} ->
    {scope : Scope sourceContext targetContext} ->
    {closingEnv : OperationalEnvironment.ClosingEnv sig []} ->
    StoreEnvironment sourceContext sourceStore valuation targetContext
      scope closingEnv -> scope.Coherent
| _, _, _, _, _, _, _, _, _, .empty => Scope.Coherent.empty
| _, _, _, _, _, _, _, _, _, .nativeWeaken older _ _ => coherent older
  | _, _, _, _, _, _, _, _, _,
    .extend older typing _ _ _ _ _ _ _ _ _ _ _ _ =>
    TermTranslation.compiledBinder_coherent (coherent older) typing.typeWf
| _, _, _, _, _, _, _, _, _, .alias older typing _ _ _ _ =>
    TermTranslation.compiledBinder_coherent (coherent older) typing.typeWf
| _, _, _, _, _, _, _, _, _,
    .bindLocation older sourceWf _ _ _ _ _ _ _ =>
    TermTranslation.compiledBinder_coherent (coherent older) sourceWf

/-- The closing substitution is an explicit environment index.  Making it
an index allows the next slot's behavior and readiness to be stated only
after all older target variables have been closed. -/
def closing
    {lexical : Nat} {sourceContext : LambdaPFC.Ctx lexical}
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closingEnv : OperationalEnvironment.ClosingEnv sig []}
    (_ : StoreEnvironment sourceContext sourceStore valuation targetContext
      scope closingEnv) : OperationalEnvironment.ClosingEnv sig [] :=
  closingEnv

/-- A native-only allocation does not change the target closing
substitution of this lexical view. -/
@[simp] theorem closing_nativeWeaken
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closingEnv : OperationalEnvironment.ClosingEnv sig []}
    (older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closingEnv)
    (runtimeValue : LambdaPFC.Tm current)
    (runtimeReady : runtimeValue.IsValue) :
    (StoreEnvironment.nativeWeaken older runtimeValue runtimeReady).closing =
      closingEnv :=
  rfl

@[simp] theorem closing_extend
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {olderClosing : OperationalEnvironment.ClosingEnv sig []}
    (older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope olderClosing)
    {sourceTerm : LambdaPFC.Tm lexical}
    {sourceType : LambdaPFC.Ty lexical}
    (typing : Fragment.HasType sourceContext sourceTerm sourceType)
    (native : TypedCode)
    (nativeValuation : SourceValuation native.arity current)
    (nativeAdmissible : OperationallyAdmissible native.typing)
    (nativeEvidence : ApplicationValueEvidence native.typing)
    {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
    {nativeScope : Scope native.context nativeTargetContext}
    {nativeClosing : OperationalEnvironment.ClosingEnv nativeSig []}
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
      behavior.argument) :
    (StoreEnvironment.extend older typing native nativeValuation
      nativeAdmissible nativeEvidence nativeEnvironment nativeReady
      runtimeReady runtime_eq
      memberCell functionCell behavior normalizes).closing =
      extendClosing olderClosing
        (TermTranslation.compileBinder scope typing.typeWf).plan behavior :=
  rfl

@[simp] theorem closing_alias
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {olderClosing : OperationalEnvironment.ClosingEnv sig []}
    (older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope olderClosing)
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
      behavior.argument) :
    (StoreEnvironment.alias older typing memberCell functionCell behavior
      normalizes).closing =
      extendClosing olderClosing
        (TermTranslation.compileBinder scope typing.typeWf).plan behavior :=
  rfl

/-! ## Static member indices agree with native pair heads -/

/-- A statically bound member package points to a native type-package cell
whose stored first component is exactly the valuation of the statically
tracked `first` index.  Allocation supplies the canonical-head premise;
aliases preserve it; later allocations merely weaken it. -/
theorem boundMember_cell
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closingEnv : OperationalEnvironment.ClosingEnv sig []}
    (store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closingEnv)
    {package first : Fin lexical} {label : LambdaPFC.Name}
    {lower upper : LambdaPFC.Ty lexical}
    (member : Fragment.BoundMember sourceContext package label lower upper
      first) :
    Exists fun witness : LambdaPFC.Ty current =>
      LambdaPFC.Store.Binds sourceStore (valuation package)
        (.pair (valuation first) label (.type witness)) := by
  induction store with
  | empty => cases member
  | nativeWeaken older runtimeValue runtimeReady ih =>
      rcases ih member with ⟨witness, binds⟩
      exact ⟨witness.weaken, .there binds⟩
  | extend older typing native nativeValuation nativeAdmissible nativeEvidence
      nativeEnvironment nativeReady runtimeReady runtime_eq memberCell
      functionCell behavior normalizes ih =>
      cases member with
      | here => exact memberCell rfl
      | there olderMember =>
          rcases ih olderMember with ⟨witness, binds⟩
          exact ⟨witness.weaken, .there binds⟩
  | alias older typing memberCell functionCell behavior normalizes ih =>
      cases member with
      | here => exact memberCell rfl
      | there olderMember => exact ih olderMember
  | bindLocation older sourceWf location binds compiled nativeEnvironment
      memberCell functionCell behavior ih =>
      cases member with
      | here => exact memberCell rfl
      | there olderMember => exact ih olderMember

/-- Repackage `boundMember_cell` in the form consumed by an alias
constructor.  This is the common exact-member case where a new lexical name
simply aliases an already-bound member package. -/
theorem memberCellOfBoundMember
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closingEnv : OperationalEnvironment.ClosingEnv sig []}
    (store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closingEnv)
    {package first : Fin lexical} {label : LambdaPFC.Name}
    {lower upper : LambdaPFC.Ty lexical}
    (member : Fragment.BoundMember sourceContext package label lower upper
      first) :
    MemberCell (Fragment.memberPackageTy first label lower upper)
      sourceStore valuation (valuation package) := by
  intro otherFirst otherLabel otherLower otherUpper typeEq
  have parts := Fragment.memberPackageTy_injective typeEq
  cases parts.1
  cases parts.2.1
  exact store.boundMember_cell member

/-- Every statically supported fragment path resolves to its static referent
under a valuation-indexed store environment. -/
theorem resolvePath
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closingEnv : OperationalEnvironment.ClosingEnv sig []}
    (store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closingEnv)
    {path : LambdaPFC.Path lexical}
    {sourceType : LambdaPFC.Ty lexical}
    (typing : Fragment.PathTy sourceContext path sourceType) :
    LambdaPFC.Path.Resolve (path.rename valuation) sourceStore
      (.loc (valuation (pathReferentIndex typing))) := by
  cases typing with
  | var => exact .var
  | exactFst member =>
      rcases store.boundMember_cell member with ⟨witness, binds⟩
      exact .fst .var binds

/-- A typed, behavioral source cell located in a native store. -/
structure LocatedBinding
    {lexical : Nat} {sourceContext : LambdaPFC.Ctx lexical}
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closingEnv : OperationalEnvironment.ClosingEnv sig []}
    (store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closingEnv)
    (index : Fin lexical) : Type where
  runtimeValue : LambdaPFC.Tm current
  binds : LambdaPFC.Store.Binds sourceStore (valuation index) runtimeValue
  /-- Native allocation provenance at the resolved location. -/
  compiled : CompiledBinding runtimeValue
  /-- The lexical environment in which the native code closure originated.
  It is carried with the physical cell and weakened through every later
  allocation, independently of the adapted lexical `slot` below. -/
  nativeTargetSig : Sig
  nativeTargetContext : Ctx nativeTargetSig
  nativeScope : Scope compiled.native.context nativeTargetContext
  nativeClosing : OperationalEnvironment.ClosingEnv nativeTargetSig []
  nativeEnvironment : StoreEnvironment compiled.native.context sourceStore
    compiled.nativeValuation nativeTargetContext nativeScope nativeClosing
  /-- Adapted behavior installed for this lexical source slot.  For an alias
  this may differ from `compiled.slot`. -/
  slot : LexicalSlot
  /-- Valuation belonging to the adapted lexical slot's original code. -/
  slotValuation : SourceValuation slot.arity current
  /-- Canonical package-head provenance at this lexical location. -/
  memberCell : MemberCell slot.sourceType sourceStore
    slotValuation (valuation index)
  /-- Canonical abstraction-head provenance at this lexical location. -/
  functionCell : FunctionCell slot.sourceType sourceStore
    slotValuation (valuation index)

/-- Look up the allocated cell denoted by a lexical source variable.

The recursive case weakens the retained original-code closure rather than
retyping the current store value. -/
noncomputable def lookup
    {lexical : Nat} {sourceContext : LambdaPFC.Ctx lexical}
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closingEnv : OperationalEnvironment.ClosingEnv sig []}
    (store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closingEnv) (index : Fin lexical) :
    LocatedBinding store index := by
  induction store with
  | empty => exact Fin.elim0 index
  | nativeWeaken older runtimeValue runtimeReady ih =>
      let found := ih index
      exact
        { runtimeValue := found.runtimeValue.weaken
          binds := .there found.binds
          compiled := found.compiled.weaken
          nativeTargetSig := found.nativeTargetSig
          nativeTargetContext := found.nativeTargetContext
          nativeScope := found.nativeScope
          nativeClosing := found.nativeClosing
          nativeEnvironment := found.nativeEnvironment.nativeWeaken
            runtimeValue runtimeReady
          slot := found.slot
          slotValuation := found.slotValuation.weaken
          memberCell := MemberCell.weaken
            (valuation := found.slotValuation) found.memberCell runtimeValue
            runtimeReady
          functionCell := FunctionCell.weaken
            (valuation := found.slotValuation) found.functionCell runtimeValue
            runtimeReady }
  | @extend lexical current sourceContext sourceStore valuation sig
      targetContext scope olderClosing older sourceTerm sourceType typing
      native nativeValuation nativeAdmissible nativeEvidence nativeSig
      nativeTargetContext nativeScope nativeClosing nativeEnvironment
      nativeReady runtimeValue runtimeReady runtime_eq memberCell functionCell
      behavior normalizes ih =>
      refine Fin.cases ?_ (fun olderIndex => ?_) index
      · let original := TypedCode.ofTyping typing
        let compilation : TypedCode.Compilation original :=
          { targetSig := sig
            targetContext := targetContext
            scope := scope
            coherent := older.coherent }
        let slot : CompiledSlot :=
          { original := original
            compilation := compilation
            environment := older.closing
            behavior := behavior
            normalizes := normalizes }
        let newest : CompiledBinding runtimeValue :=
          { slot := slot
            native := native
            nativeValuation := nativeValuation
            nativeAdmissible := nativeAdmissible
            nativeEvidence := nativeEvidence
            nativeTargetSig := nativeSig
            nativeTargetContext := nativeTargetContext
            nativeScope := nativeScope
            nativeClosing := nativeClosing
            nativeReady := nativeReady
            runtime_eq := runtime_eq }
        exact
          { runtimeValue := runtimeValue.weaken
            binds := .here
            compiled := newest.weaken
            nativeTargetSig := nativeSig
            nativeTargetContext := nativeTargetContext
            nativeScope := nativeScope
            nativeClosing := nativeClosing
            nativeEnvironment := nativeEnvironment.nativeWeaken runtimeValue
              runtimeReady
            slot := slot.lexical
            slotValuation := valuation.weaken
            memberCell := memberCell
            functionCell := functionCell }
      · let found := ih olderIndex
        exact
          { runtimeValue := found.runtimeValue.weaken
            binds := .there found.binds
            compiled := found.compiled.weaken
            nativeTargetSig := found.nativeTargetSig
            nativeTargetContext := found.nativeTargetContext
            nativeScope := found.nativeScope
            nativeClosing := found.nativeClosing
            nativeEnvironment := found.nativeEnvironment.nativeWeaken
              runtimeValue runtimeReady
            slot := found.slot
            slotValuation := found.slotValuation.weaken
            memberCell := MemberCell.weaken
              (valuation := found.slotValuation) found.memberCell runtimeValue
              runtimeReady
            functionCell := FunctionCell.weaken
              (valuation := found.slotValuation) found.functionCell runtimeValue
              runtimeReady }
  | @alias lexical current sourceContext sourceStore valuation sig
      targetContext scope olderClosing older path sourceType typing memberCell
      functionCell behavior normalizes ih =>
      refine Fin.cases ?_ (fun olderIndex => ?_) index
      · let referent := ih (typedPathReferent typing)
        let slot : LexicalSlot :=
          { arity := lexical
            context := sourceContext
            sourceType := sourceType
            sourceWf := typing.typeWf
            targetSig := sig
            targetContext := targetContext
            scope := scope
            environment := older.closing
            behavior := behavior }
        exact
          { runtimeValue := referent.runtimeValue
            binds := referent.binds
            compiled := referent.compiled
            nativeTargetSig := referent.nativeTargetSig
            nativeTargetContext := referent.nativeTargetContext
            nativeScope := referent.nativeScope
            nativeClosing := referent.nativeClosing
            nativeEnvironment := referent.nativeEnvironment
            slot := slot
            slotValuation := valuation
            memberCell := memberCell
            functionCell := functionCell }
      · let found := ih olderIndex
        exact
          { runtimeValue := found.runtimeValue
            binds := found.binds
            compiled := found.compiled
            nativeTargetSig := found.nativeTargetSig
            nativeTargetContext := found.nativeTargetContext
            nativeScope := found.nativeScope
            nativeClosing := found.nativeClosing
            nativeEnvironment := found.nativeEnvironment
            slot := found.slot
            slotValuation := found.slotValuation
            memberCell := found.memberCell
            functionCell := found.functionCell }
  | @bindLocation lexical current sourceContext sourceStore valuation sig
      targetContext scope olderClosing older sourceType sourceWf location
      runtimeValue binds compiled nativeSig nativeTargetContext nativeScope
      nativeClosing nativeEnvironment memberCell functionCell behavior ih =>
      refine Fin.cases ?_ (fun olderIndex => ?_) index
      · let slot : LexicalSlot :=
          { arity := lexical
            context := sourceContext
            sourceType := sourceType
            sourceWf := sourceWf
            targetSig := sig
            targetContext := targetContext
            scope := scope
            environment := older.closing
            behavior := behavior }
        exact
          { runtimeValue := runtimeValue
            binds := binds
            compiled := compiled
            nativeTargetSig := nativeSig
            nativeTargetContext := nativeTargetContext
            nativeScope := nativeScope
            nativeClosing := nativeClosing
            nativeEnvironment := nativeEnvironment
            slot := slot
            slotValuation := valuation
            memberCell := memberCell
            functionCell := functionCell }
      · let found := ih olderIndex
        exact
          { runtimeValue := found.runtimeValue
            binds := found.binds
            compiled := found.compiled
            nativeTargetSig := found.nativeTargetSig
            nativeTargetContext := found.nativeTargetContext
            nativeScope := found.nativeScope
            nativeClosing := found.nativeClosing
            nativeEnvironment := found.nativeEnvironment
            slot := found.slot
            slotValuation := found.slotValuation
            memberCell := found.memberCell
            functionCell := found.functionCell }

/-! The alias lookup equations make the split explicit: the newest lexical
slot has fresh adapted target behavior, while its native value and allocation
provenance are exactly those of the static referent. -/

@[simp] theorem lookup_alias_here_runtimeValue
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {olderClosing : OperationalEnvironment.ClosingEnv sig []}
    (older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope olderClosing)
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
      behavior.argument) :
    (lookup (.alias older typing memberCell functionCell behavior normalizes)
      0).runtimeValue =
      (lookup older (typedPathReferent typing)).runtimeValue :=
  rfl

@[simp] theorem lookup_alias_here_compiled
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {olderClosing : OperationalEnvironment.ClosingEnv sig []}
    (older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope olderClosing)
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
      behavior.argument) :
    (lookup (.alias older typing memberCell functionCell behavior normalizes)
      0).compiled =
      (lookup older (typedPathReferent typing)).compiled :=
  rfl

@[simp] theorem lookup_alias_here_slot_sourceType
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {olderClosing : OperationalEnvironment.ClosingEnv sig []}
    (older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope olderClosing)
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
      behavior.argument) :
    (lookup (.alias older typing memberCell functionCell behavior normalizes)
      0).slot.sourceType = sourceType :=
  rfl

@[simp] theorem lookup_alias_there_runtimeValue
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {olderClosing : OperationalEnvironment.ClosingEnv sig []}
    (older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope olderClosing)
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
    (index : Fin lexical) :
    (lookup (.alias older typing memberCell functionCell behavior normalizes)
      index.succ).runtimeValue =
      (lookup older index).runtimeValue :=
  rfl

end StoreEnvironment

end OperationalStoreEnvironment
end LambdaPToFCo
