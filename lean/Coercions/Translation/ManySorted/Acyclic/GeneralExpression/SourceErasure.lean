import Coercions.DOT.Captures.Acyclic.GeneralExpression.Erasure
import Coercions.Translation.ManySorted.Acyclic.SourceErasure

/-!
# Context-indexed erasure of general captured-DOT expressions

The general-expression source defines its runtime erasure independently of
the compiler.  This module equips that erasure with the canonical runtime
variable projection induced by the existing many-sorted target layout.

The source context, variables, and static language are shared with the
value-MNF fragment.  Consequently its established `compiledRenaming` and
term-count theorem apply unchanged: an expanded object contributes many
static target coordinates but exactly one runtime payload coordinate.
-/

namespace DOTCaptureToManySortedFC.Acyclic.GeneralExpression.SourceErasure

namespace Source

export DOTCapture.Acyclic.GeneralExpression
  (Scope Var Path Ctx Value Term ValueLabel Capture Ty ObjectSig)

end Source

namespace Direct

export DOTCapture.Acyclic.GeneralExpression.Erasure
  (Renaming erasePathWith eraseValueWith eraseTermWith)

end Direct

namespace CoreErasure

export DOTCaptureToManySortedFC.Acyclic.SourceErasure
  (targetTermCount compiledRenaming compiledRenaming_apply)

end CoreErasure

/-! ## Canonical target-layout projection -/

/-- Every general-expression source binder still contributes exactly one
runtime coordinate in the translated target layout. -/
@[simp]
theorem targetTermCount {scope : Source.Scope} (context : Source.Ctx scope) :
    (Layout.sig context).termCount = scope :=
  CoreErasure.targetTermCount context

/-- The canonical source-variable projection is shared with the value-MNF
compiler because both languages use the same contexts and variables. -/
abbrev compiledRenaming {scope : Source.Scope} (context : Source.Ctx scope) :
    Direct.Renaming scope (Layout.sig context).termCount :=
  CoreErasure.compiledRenaming context

@[simp]
theorem compiledRenaming_apply {scope : Source.Scope}
    (context : Source.Ctx scope) (index : Source.Var scope) :
    compiledRenaming context index =
      ManySortedFC.BVar.toTermIndex (Layout.termVar context index) := rfl

/-- Extending a source context adds the same newest runtime coordinate as
lifting its canonical variable projection.  `HEq` hides the static target
coordinates contributed by an object expansion. -/
theorem compiledRenaming_extend {scope : Source.Scope}
    (context : Source.Ctx scope) (type : Source.Ty scope) :
    HEq (compiledRenaming (context.extendTerm type))
      (DOTCapture.Acyclic.GeneralExpression.Erasure.Renaming.lift
        (compiledRenaming context)) := by
  cases type with
  | top | bot | one | ref | arr | object =>
      apply heq_of_eq
      funext index
      cases index <;> rfl
  | capturing captures shape =>
      cases shape <;>
        apply heq_of_eq <;>
        funext index <;>
        cases index <;> rfl

/-! ## Context-indexed direct erasure -/

/-- Erase a surface value in the runtime scope induced by its source
context's target layout. -/
def eraseValue {scope : Source.Scope} (context : Source.Ctx scope)
    (value : Source.Value scope) :
    ManySortedFC.Runtime.Tm (Layout.sig context).termCount :=
  Direct.eraseValueWith (compiledRenaming context) value

/-- Erase a general surface computation in the runtime scope induced by its
source context's target layout. -/
def eraseTerm {scope : Source.Scope} (context : Source.Ctx scope)
    (term : Source.Term scope) :
    ManySortedFC.Runtime.Tm (Layout.sig context).termCount :=
  Direct.eraseTermWith (compiledRenaming context) term

/-! ## Exact constructor equations -/

@[simp]
theorem eraseValue_var {scope : Source.Scope} (context : Source.Ctx scope)
    (name : Source.Var scope) :
    eraseValue context (.var name) =
      .var (ManySortedFC.BVar.toTermIndex
        (Layout.termVar context name)) := rfl

@[simp]
theorem eraseValue_unit {scope : Source.Scope} (context : Source.Ctx scope) :
    eraseValue context (.unit : Source.Value scope) = .unit := rfl

@[simp]
theorem eraseValue_lam {scope : Source.Scope} (context : Source.Ctx scope)
    (domain codomain : Source.Ty scope)
    (body : Source.Term (scope + 1)) :
    eraseValue context (.lam domain codomain body) =
      .lam (Direct.eraseTermWith (compiledRenaming context).lift body) := rfl

@[simp]
theorem eraseValue_object {scope : Source.Scope} (context : Source.Ctx scope)
    (signature : Source.ObjectSig scope) (typeWitness : Source.Ty scope)
    (captureWitness : Source.Capture scope)
    (payload : Source.Value scope) :
    eraseValue context
        (.object signature typeWitness captureWitness payload) =
      eraseValue context payload := rfl

@[simp]
theorem eraseTerm_ret {scope : Source.Scope} (context : Source.Ctx scope)
    (value : Source.Value scope) :
    eraseTerm context (.ret value) = eraseValue context value := rfl

@[simp]
theorem eraseTerm_select {scope : Source.Scope} (context : Source.Ctx scope)
    (receiver : Source.Path scope) :
    eraseTerm context (.select receiver .v) =
      .var (ManySortedFC.BVar.toTermIndex
        (Layout.translatePath context receiver)) := by
  cases receiver
  rfl

@[simp]
theorem eraseTerm_app {scope : Source.Scope} (context : Source.Ctx scope)
    (function argument : Source.Term scope) :
    eraseTerm context (.app function argument) =
      .app (eraseTerm context function) (eraseTerm context argument) := rfl

@[simp]
theorem eraseTerm_let {scope : Source.Scope} (context : Source.Ctx scope)
    (result : Source.Ty scope) (rhs : Source.Term scope)
    (body : Source.Term (scope + 1)) :
    eraseTerm context (.let' result rhs body) =
      .let' (eraseTerm context rhs)
        (Direct.eraseTermWith (compiledRenaming context).lift body) := rfl

/-! ## Agreement with generated primitive selection -/

/-- Primitive selection generated by the shared exposure compiler erases to
the same payload coordinate as the independently defined surface selection. -/
theorem generatedSelection_erase {scope : Source.Scope}
    {context : Source.Ctx scope}
    {translated : ExposureTranslation.TranslatedContext context}
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (resolved : ExposureTranslation.ResolvedExposure translated receiver
      signature) :
    (SelectionTranslation.term resolved).erase =
      eraseTerm context (.select receiver .v) := by
  simpa [eraseTerm,
    DOTCapture.Acyclic.GeneralExpression.Erasure.eraseTermWith,
    DOTCaptureToManySortedFC.Acyclic.SourceErasure.eraseTerm,
    DOTCaptureToManySortedFC.Acyclic.SourceErasure.eraseTermWith] using
    DOTCaptureToManySortedFC.Acyclic.SourceErasure.generatedSelection_erase
      resolved

end DOTCaptureToManySortedFC.Acyclic.GeneralExpression.SourceErasure
