import LambdaPToFCo.OperationalApplicationTranslation
import LambdaPToFCo.OperationalStoreEnvironment

/-!
# Store-facing bridge for compiled function application

This module connects the target application macro to a function cell returned
by `StoreEnvironment.lookup`.  The crucial premise is explicit:
`CompiledBindingFunction` says that the native cell's retained original typing
derivation is a syntactic abstraction and carries `ClosedFunctionEvidence`.
An arbitrary ready behavioral slot is not silently treated as a closure.

The proof uses determinism only to identify two target normal forms of the
same closed retained compilation:

* `FunctionView.normalize` exposes its canonical lambda/arrow-cast value;
* the store cell's previously supplied normalization exposes its behavioral
  argument.

Once those values are equal, `ArgumentEvidence` supplies the layerwise
contravariant adaptations and the target-only application theorem applies.
No source store realization or source typing reconstruction is used here.
-/

namespace LambdaPToFCo
namespace OperationalApplicationStore

open SystemFCo
open OperationalApplication
open OperationalApplicationTranslation
open OperationalBindingView
open OperationalStoreEnvironment

/-! ## Uniqueness of deterministic target normal forms -/

/-- Two target values reached from one expression by deterministic reduction
are syntactically equal. -/
theorem value_endpoint_unique
    (first : Exp.Steps expression firstValue)
    (second : Exp.Steps expression secondValue)
    (firstReady : Exp.IsValue firstValue)
    (secondReady : Exp.IsValue secondValue) :
    firstValue = secondValue := by
  induction first generalizing secondValue with
  | refl => exact firstReady.steps_eq second
  | tail reduction rest ih =>
      cases second with
      | refl => exact False.elim (secondReady.not_step reduction)
      | tail reduction' rest' =>
          cases reduction.deterministic reduction'
          exact ih rest' firstReady secondReady

/-- Elaborating a derivation transported only along its term index gives the
same target syntax once the transported derivation is identified. -/
theorem elaborate_term_transport
    {sourceContext : LambdaPFC.Ctx n}
    {targetContext : Ctx sig}
    (scope : StaticTranslation.Scope sourceContext targetContext)
    {term term' : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n}
    (term_eq : term = term')
    (typing : Fragment.HasType sourceContext term sourceType)
    (typing' : Fragment.HasType sourceContext term' sourceType)
    (typing_eq : (term_eq ▸ typing) = typing') :
    TermTranslation.elaborate scope typing' =
      TermTranslation.elaborate scope typing := by
  cases term_eq
  cases typing_eq
  rfl

/-! ## Abstraction provenance for one native cell -/

/-- The retained original derivation of a compiled native binding is really
an abstraction derivation with closed function-coercion provenance.

`nativeTyping_eq` prevents a caller from choosing an unrelated derivation
for the same term.  The separate syntactic `term_eq` is useful to the source
CK bridge, which must also identify the native stored value as an abstraction.

The native code and the adapted allocation slot intentionally have different
origins.  `behavior_eq` is therefore an explicit boundary supplied by the
closed admissible-value compiler; it is not inferred from the slot's source
derivation.
-/
structure CompiledBindingFunction
    {current : Nat} {runtimeValue : LambdaPFC.Tm current}
    (binding : CompiledBinding runtimeValue) : Type where
  compilation : OperationalCode.TypedCode.Compilation binding.native
  environment : OperationalEnvironment.ClosingEnv compilation.targetSig []
  domain : LambdaPFC.Ty binding.native.arity
  sourceBody : LambdaPFC.Tm (binding.native.arity + 1)
  term_eq : binding.native.term = .abs domain sourceBody
  typing : Fragment.HasType binding.native.context
    (.abs domain sourceBody) binding.native.resultType
  nativeTyping_eq : (term_eq ▸ binding.native.typing) = typing
  evidence : ClosedFunctionEvidence compilation.scope environment typing
  behavior_eq : evidence.image.view.normalize.value.expression =
    binding.slot.behavior.argument

namespace CompiledBindingFunction

/-- Native closure provenance really identifies the stored source value as an
abstraction under the retained source valuation. -/
theorem runtime_eq_abs
    {current : Nat} {runtimeValue : LambdaPFC.Tm current}
    {binding : CompiledBinding runtimeValue}
    (function : CompiledBindingFunction binding) :
    runtimeValue =
      LambdaPFC.Tm.abs (function.domain.rename binding.nativeValuation)
        (function.sourceBody.rename binding.nativeValuation.ext) := by
  calc
    runtimeValue =
        binding.native.term.rename binding.nativeValuation :=
      binding.runtime_eq
    _ = (LambdaPFC.Tm.abs function.domain function.sourceBody).rename
        binding.nativeValuation := by rw [function.term_eq]
    _ = LambdaPFC.Tm.abs (function.domain.rename binding.nativeValuation)
        (function.sourceBody.rename binding.nativeValuation.ext) := rfl

/-- The dependent closed image selected by this cell's retained evidence. -/
noncomputable def image
    (function : CompiledBindingFunction binding) :
    ClosedFunctionImage function.compilation.scope
      function.environment function.typing :=
  function.evidence.image

/-- The function view starts at exactly the retained cell compilation, not at
an unrelated syntactic lambda. -/
theorem expression_eq_compilation
    (function : CompiledBindingFunction binding) :
    function.image.view.expression =
      function.compilation.close function.environment := by
  rw [function.image.expression_eq]
  change function.environment.closeExp
      (TermTranslation.elaborate function.compilation.scope
        function.typing) =
    function.environment.closeExp
      (TermTranslation.elaborate function.compilation.scope
        binding.native.typing)
  exact congrArg function.environment.closeExp
    (elaborate_term_transport function.compilation.scope
      function.term_eq binding.native.typing function.typing
      function.nativeTyping_eq)

/-- The canonical function value exposed by `FunctionView` is the behavioral
argument already installed in the compiled allocation cell. -/
theorem canonical_eq_behavior
    (function : CompiledBindingFunction binding) :
    function.image.view.normalize.value.expression =
      binding.slot.behavior.argument :=
  function.behavior_eq

/-- A normalization theorem from the separate native compilation is another
sound way to establish the explicit native/slot boundary. -/
theorem canonical_eq_behavior_of_normalizes
    (function : CompiledBindingFunction binding)
    (normalizes : Exp.Steps
      (function.compilation.close function.environment)
      binding.slot.behavior.argument) :
    function.image.view.normalize.value.expression =
      binding.slot.behavior.argument := by
  have functionSteps : Exp.Steps
      (function.compilation.close function.environment)
      function.image.view.normalize.value.expression := by
    rw [← function.expression_eq_compilation]
    exact function.image.view.normalize.reductions
  exact value_endpoint_unique functionSteps normalizes
    function.image.view.normalize.value.ready binding.slot.behavior.ready

/-- Apply the behavioral value installed in this allocation cell.  The outer
argument view may be ordinary or exact; `ArgumentEvidence` records every
contravariant adaptation down to the base function binder. -/
noncomputable def application
    (function : CompiledBindingFunction binding)
    {argumentPlan : Interface.BinderPlan []}
    (argument : EliminationView argumentPlan)
    (argumentEvidence : ArgumentEvidence
      function.image.view.normalize.value argument) :
    ApplicationView function.image.body binding.slot.behavior.argument
      argument.argument := by
  rw [← function.canonical_eq_behavior]
  exact function.image.view.normalize.value.application
    argumentEvidence.toArgumentView

end CompiledBindingFunction

/-! ## Lookup-level application -/

/-- Application-side bridge for two lexical locations in a compiled source
store.  The function uses native allocation provenance from `compiled`; the
argument uses the possibly adapted behavioral view of its lexical `slot`.

This theorem intentionally stops at `ApplicationView`.  Connecting its
instantiated body and residual result context to the source CK successor also
needs the source valuation/opening equations and belongs to the final step
simulation theorem. -/
noncomputable def lookup_application
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : OperationalCode.SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : StaticTranslation.Scope sourceContext targetContext}
    {closing : OperationalEnvironment.ClosingEnv sig []}
    (store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (functionIndex argumentIndex : Fin lexical)
    (function : CompiledBindingFunction
      (store.lookup functionIndex).compiled)
    (argumentEvidence : ArgumentEvidence
      function.image.view.normalize.value
      (store.lookup argumentIndex).slot.behavior) :
    ApplicationView function.image.body
      (store.lookup functionIndex).compiled.slot.behavior.argument
      (store.lookup argumentIndex).slot.behavior.argument :=
  function.application (store.lookup argumentIndex).slot.behavior
    argumentEvidence

/-- Variant for the lexical function slot itself.  Direct function variables
have this equality definitionally; aliases can provide it after proving that
their adapted function view agrees with the native cell's canonical value. -/
noncomputable def lookup_slot_application
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : OperationalCode.SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : StaticTranslation.Scope sourceContext targetContext}
    {closing : OperationalEnvironment.ClosingEnv sig []}
    (store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (functionIndex argumentIndex : Fin lexical)
    (function : CompiledBindingFunction
      (store.lookup functionIndex).compiled)
    (functionSlot_eq :
      (store.lookup functionIndex).slot.behavior.argument =
        (store.lookup functionIndex).compiled.slot.behavior.argument)
    (argumentEvidence : ArgumentEvidence
      function.image.view.normalize.value
      (store.lookup argumentIndex).slot.behavior) :
    ApplicationView function.image.body
      (store.lookup functionIndex).slot.behavior.argument
      (store.lookup argumentIndex).slot.behavior.argument := by
  rw [functionSlot_eq]
  exact lookup_application store functionIndex argumentIndex function
    argumentEvidence

end OperationalApplicationStore
end LambdaPToFCo
