import Coercions.Translation.ManySorted.BinderOnly.TermElaborationErasure
import Coercions.ManySortedFC.TermCheckerCompleteness

/-!
# Quantified capture coercion examples

The examples use one ambient capability `a` and one abstract capture `c`.
They exercise source interval entailment, quantified source adapters, target
checking, and runtime erasure on actual function values.
-/

namespace DOTCaptureToManySortedFC.BinderOnly
namespace QuantifiedCoercionExamples

open DOTCapture.BinderOnly
open DOTCapture.BinderOnly.TypingExamples

abbrev SourceScope : Sig := ([] : Sig) ▹ .term

def sourceContext : Ctx SourceScope :=
  outerCapabilityContext

def ambientCapability : Capture SourceScope :=
  .singleton (.var .here)

/-- `N` requires the abstract capture to be empty. -/
def N : Interval .capture SourceScope :=
  .bounds .none (.some (.capture .empty))

/-- `W` permits the abstract capture to contain `a`. -/
def W : Interval .capture SourceScope :=
  .bounds .none (.some (.capture ambientCapability))

def narrowContext : Ctx (SourceScope ▹ .static .capture) :=
  sourceContext.extendStatic N

def wideContext : Ctx (SourceScope ▹ .static .capture) :=
  sourceContext.extendStatic W

def abstractCapture : Capture (SourceScope ▹ .static .capture) :=
  .ref (.bound .here)

def narrowUpper : CaptureIncludes narrowContext abstractCapture .empty := by
  change Includes narrowContext
    (StaticRef.bound (.here : BVar
      (SourceScope ▹ .static .capture) (.static .capture))).expression
    (.capture .empty)
  exact .upper (.bound rfl)

def emptyIncludesAmbientUnderN :
    CaptureIncludes narrowContext .empty
      (ambientCapability.weaken (kind := .static .capture)) :=
  .captureEmpty

/-- Under `N`, the upper assumption gives `c ⊆ ∅`; transitivity with
`∅ ⊆ {a}` establishes the obligation exported by `W`. -/
def NtoW : Interval.Entails sourceContext N W :=
  .upper (.trans narrowUpper emptyIncludesAmbientUnderN)

/-- A closed unary function whose retained capture is the abstract `c`. -/
def quantifiedBody : Ty (SourceScope ▹ .static .capture) :=
  .capturing abstractCapture (.arr .one .one)

def staticBody : Value (SourceScope ▹ .static .capture) :=
  .lam .one .one (.ret (.var .here))

def staticBodyTyping :
    Value.HasType (sourceContext.extendStatic W) staticBody quantifiedBody := by
  apply Value.HasType.adapt
  · exact Value.HasType.lam (closure := .empty)
      (.ret .var) .captureEmpty
  · exact .captured .captureEmpty .identity

def forallWType : Ty SourceScope :=
  .capturing ambientCapability (.forallI W quantifiedBody)

def forallNType : Ty SourceScope :=
  .capturing ambientCapability (.forallI N quantifiedBody)

def forallWValue : Value SourceScope :=
  .staticLam W staticBody

def wideUpper : CaptureIncludes wideContext abstractCapture
    (ambientCapability.weaken (kind := .static .capture)) := by
  change Includes wideContext
    (StaticRef.bound (.here : BVar
      (SourceScope ▹ .static .capture) (.static .capture))).expression
    (.capture (ambientCapability.weaken (kind := .static .capture)))
  exact .upper (.bound rfl)

/-- The static body retains `c`, and `W` discharges it to the ambient `a`. -/
def forallWTyping :
    Value.HasType sourceContext forallWValue forallWType :=
  .staticLam staticBodyTyping wideUpper

def forallCoercion : Adapts sourceContext forallWType forallNType :=
  .captured .refl (.forallBounds NtoW .identity)

def forallNTyping :
    Value.HasType sourceContext forallWValue forallNType :=
  .adapt forallWTyping forallCoercion

def compiledForall := compileValue forallNTyping

theorem compiled_forall_is_accepted :
    ManySortedFC.Tm.synth (translateContext sourceContext)
        compiledForall.term =
      some (.empty, translateTy sourceContext forallNType) :=
  ManySortedFC.Tm.synth_complete compiledForall.typing

@[simp]
theorem forall_source_erases_to_lambda :
    SourceErasure.eraseValue sourceContext forallWValue =
      ManySortedFC.Runtime.Tm.lam (.var 0) := by
  rfl

theorem compiled_forall_erases_exactly_to_lambda :
    compiledForall.term.erase =
      ManySortedFC.Runtime.Tm.lam (.var 0) := by
  rfl

theorem compiled_forall_erases_administratively_to_lambda :
    ManySortedFC.Runtime.AdministrativeEq
      compiledForall.term.erase (.lam (.var 0)) := by
  simpa only [forall_source_erases_to_lambda] using
    compileValue_erase_admin forallNTyping

/-! ## Existential widening -/

def payloadValue : Value SourceScope :=
  .lam .one .one (.ret (.var .here))

def payloadTyping :
    Value.HasType sourceContext payloadValue
      (quantifiedBody.instantiateStatic (.capture .empty)) := by
  change Value.HasType sourceContext payloadValue
    (.capturing .empty (.arr .one .one))
  exact .lam (.ret .var) .captureEmpty

def emptySatisfiesN :
    Interval.SatisfiedBy sourceContext (.capture .empty) N :=
  .upper .refl

def existsNType : Ty SourceScope :=
  .capturing .empty (.existsI N quantifiedBody)

def existsWType : Ty SourceScope :=
  .capturing ambientCapability (.existsI W quantifiedBody)

def packedNValue : Value SourceScope :=
  .pack N quantifiedBody (.capture .empty) payloadValue

def packedNTyping :
    Value.HasType sourceContext packedNValue existsNType :=
  .pack emptySatisfiesN payloadTyping .refl

def existsCoercion : Adapts sourceContext existsNType existsWType :=
  .captured .captureEmpty (.existsBounds NtoW .identity)

def packedWTyping :
    Value.HasType sourceContext packedNValue existsWType :=
  .adapt packedNTyping existsCoercion

def compiledExists := compileValue packedWTyping

theorem compiled_exists_is_accepted :
    ManySortedFC.Tm.synth (translateContext sourceContext)
        compiledExists.term =
      some (.empty, translateTy sourceContext existsWType) :=
  ManySortedFC.Tm.synth_complete compiledExists.typing

@[simp]
theorem package_source_erases_to_lambda :
    SourceErasure.eraseValue sourceContext packedNValue =
      ManySortedFC.Runtime.Tm.lam (.var 0) := by
  rfl

theorem compiled_exists_erases_exactly_to_lambda :
    compiledExists.term.erase =
      ManySortedFC.Runtime.Tm.lam (.var 0) := by
  rfl

theorem compiled_exists_erases_administratively_to_lambda :
    ManySortedFC.Runtime.AdministrativeEq
      compiledExists.term.erase (.lam (.var 0)) := by
  simpa only [package_source_erases_to_lambda] using
    compileValue_erase_admin packedWTyping

/-! ## Compiled adapter shape -/

def hasCapturedForallMorphism {scope : ManySortedFC.Sig} :
    ManySortedFC.Adapter scope → Bool
  | .captured _ (.forallMorphism _ _ _ _) => true
  | _ => false

def hasCapturedExistsMorphism {scope : ManySortedFC.Sig} :
    ManySortedFC.Adapter scope → Bool
  | .captured _ (.existsMorphism _ _ _ _) => true
  | _ => false

theorem compiled_forall_adapter_has_morphism :
    hasCapturedForallMorphism (compileAdapts forallCoercion).adapter = true := by
  native_decide

theorem compiled_exists_adapter_has_morphism :
    hasCapturedExistsMorphism (compileAdapts existsCoercion).adapter = true := by
  native_decide

end QuantifiedCoercionExamples
end DOTCaptureToManySortedFC.BinderOnly
