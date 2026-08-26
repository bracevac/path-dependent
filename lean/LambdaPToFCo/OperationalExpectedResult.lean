import LambdaPToFCo.OperationalFunctionResultProvenance
import LambdaPToFCo.OperationalResultContext

/-!
# Proof-relevant result-interface adapters

A generated result context only says that it maps a ready closed expression
to some ready closed expression.  Machine simulation needs more: the endpoint
must implement the binder interface expected by the suspended source
computation, including the syntactic path-coherence laws used by later path
translation.

`ResultBoundary` packages such an expected interface without fixing its
source provenance.  `ExpectedResultAdapter` is a proof-relevant transformer
between boundaries.  Its identity and composition operations follow the
nesting order of `ResultContext` exactly.  The ordinary constructor is the
one used by the restricted application core: it normalizes the generated
target context, rebuilds a direct ordinary binder view around the resulting
value, and proves the local path laws.  Exact-member outputs deliberately
have no analogous provenance-free constructor.
-/

namespace LambdaPToFCo
namespace OperationalExpectedResult

universe u v w

open SystemFCo
open StaticTranslation
open OperationalEnvironment
open OperationalBindingView
open OperationalApplication
open OperationalApplicationSpine
open OperationalValueEvidence
open OperationalResultContext
open OperationalPathCoherence
open OperationalPathCoherenceGenerated
open OperationalFunctionResultProvenance

/-- A closed binder plan together with the evidence required of any view
advertised at that plan.  The evidence lives in `Type` so later restricted
coercion adapters may retain computational provenance rather than only a
proposition. -/
structure ResultBoundary where
  plan : Interface.BinderPlan []
  Accepts : EliminationView plan -> Sort u

/-- One behavioral target view accepted by a result boundary. -/
structure ResultInterface (boundary : ResultBoundary.{u}) where
  view : EliminationView boundary.plan
  accepted : boundary.Accepts view

namespace ResultInterface

/-- Transporting a result interface between equal boundary packages does
not change the closed target expression advertised by its view. -/
@[simp] theorem castBoundary_argument
    {left right : ResultBoundary.{u}} (equal : left = right)
    (interface : ResultInterface left) :
    (equal ▸ interface).view.argument = interface.view.argument := by
  cases equal
  rfl

end ResultInterface

/-- A result context which maps every accepted input interface to an
accepted output interface and exposes the exact target reduction between
their advertised arguments. -/
structure ExpectedResultAdapter
    (context : ResultContext [])
    (input : ResultBoundary.{u}) (output : ResultBoundary.{v}) where
  map : ResultInterface input -> ResultInterface output
  steps : forall interface,
    Exp.Steps (context.plug interface.view.argument)
      (map interface).view.argument

namespace ExpectedResultAdapter

/-- The empty target context preserves the complete behavioral interface. -/
def identity (boundary : ResultBoundary.{u}) :
    ExpectedResultAdapter .identity boundary boundary where
  map := fun interface => interface
  steps := fun _ => .refl

/-- Compose an outer adapter after an inner adapter. -/
def compose
    {outerContext innerContext : ResultContext []}
    {input : ResultBoundary.{u}} {middle : ResultBoundary.{v}}
    {output : ResultBoundary.{w}}
    (outer : ExpectedResultAdapter outerContext middle output)
    (inner : ExpectedResultAdapter innerContext input middle) :
    ExpectedResultAdapter (outerContext.compose innerContext) input output where
  map := fun interface => outer.map (inner.map interface)
  steps := fun interface =>
    (outerContext.steps (inner.steps interface)).trans
      (outer.steps (inner.map interface))

@[simp] theorem identity_map
    (interface : ResultInterface boundary) :
    (identity boundary).map interface = interface := rfl

@[simp] theorem compose_map
    (outer : ExpectedResultAdapter outerContext middle output)
    (inner : ExpectedResultAdapter innerContext input middle)
    (interface : ResultInterface input) :
    (outer.compose inner).map interface =
      outer.map (inner.map interface) := rfl

end ExpectedResultAdapter

/-! ## Source-indexed boundaries -/

/-- The expected closed interface of one source type in a compiled lexical
environment. -/
noncomputable def sourceBoundary
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (closing : ClosingEnv sig [])
    (arguments : ClosedArguments n) : ResultBoundary.{0} where
  plan := (TermTranslation.compileBinder scope sourceWf).plan.subst
    closing.substitution
  Accepts := fun view =>
    SourceResultAcceptance scope sourceWf closing view arguments

namespace ResultInterface

/-- Reindex a source result interface along an explicit equality of the
proof-relevant source well-formedness derivations.  This is used when a
captured frame stores both its original hole proof and the bound typing's
canonical proof. -/
noncomputable def castSourceWf
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    {left right : Fragment.Wf sourceContext sourceType}
    (equal : left = right)
    (closing : ClosingEnv sig [])
    (arguments : ClosedArguments n)
    (interface : ResultInterface
      (sourceBoundary scope right closing arguments)) :
    ResultInterface (sourceBoundary scope left closing arguments) := by
  cases equal
  exact interface

@[simp] theorem castSourceWf_argument
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    {left right : Fragment.Wf sourceContext sourceType}
    (equal : left = right)
    (closing : ClosingEnv sig [])
    (arguments : ClosedArguments n)
    (interface : ResultInterface
      (sourceBoundary scope right closing arguments)) :
    (castSourceWf scope equal closing arguments interface).view.argument =
      interface.view.argument := by
  cases equal
  rfl

end ResultInterface

/-! ## Provenance-free ordinary output -/

/-- Direct ordinary binder view around a ready closed target expression. -/
noncomputable def ordinaryView
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (shape : OrdinaryShape sourceType)
    (closing : ClosingEnv sig [])
    (value : Exp []) (ready : value.IsValue) :
    EliminationView
      ((TermTranslation.compileBinder scope sourceWf).plan.subst
        closing.substitution) := by
  let closedType := closing.closeTy (translateType scope sourceWf)
  let actual : Instantiation (.ordinary closedType) := .ordinary value
  let direct := BindingView.ofInstantiation actual ready
  have planEq :
      (Interface.BinderPlan.ordinary closedType) =
        (TermTranslation.compileBinder scope sourceWf).plan.subst
          closing.substitution := by
    rw [OperationalValueEvidence.compileBinder_plan_ordinary scope sourceWf
      shape]
    rfl
  exact EliminationView.castPlan planEq (EliminationView.ofDirect direct)

@[simp] theorem ordinaryView_argument
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (shape : OrdinaryShape sourceType)
    (closing : ClosingEnv sig [])
    (value : Exp []) (ready : value.IsValue) :
    (ordinaryView scope sourceWf shape closing value ready).argument = value := by
  dsimp only [ordinaryView]
  exact EliminationView.castPlan_argument _ _

/-- A direct ordinary result view satisfies the raw-slot law. -/
theorem ordinaryView_rawSlot
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (shape : OrdinaryShape sourceType)
    (closing : ClosingEnv sig [])
    (value : Exp []) (ready : value.IsValue) :
    RawSlot (ordinaryView scope sourceWf shape closing value ready) := by
  dsimp only [ordinaryView]
  apply rawSlot_castPlan
  exact rawSlot_ofInstantiation _ _

/-- Any generated target context can be given a source-level ordinary output
interface.  This is the restricted application's result adapter. -/
noncomputable def ofGeneratedOrdinary
    {context : ResultContext []}
    (generated : GeneratedResultContext context)
    (input : ResultBoundary.{u})
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (shape : NonCanonicalResultShape sourceType)
    (closing : ClosingEnv sig [])
    (arguments : ClosedArguments n) :
    ExpectedResultAdapter context input
      (sourceBoundary scope sourceWf closing arguments) where
  map := fun interface =>
    let normalization := generated.normalize interface.view.ready
    let view := ordinaryView scope sourceWf shape.ordinary closing
      normalization.result normalization.ready
    { view := view
      accepted :=
        SourceResultAcceptance.ofNonCanonical scope sourceWf shape closing
          view arguments
          (ordinaryView_rawSlot scope sourceWf shape.ordinary closing
            normalization.result normalization.ready) }
  steps := fun interface => by
    let normalization := generated.normalize interface.view.ready
    simpa only [ordinaryView_argument] using normalization.reductions

end OperationalExpectedResult
end LambdaPToFCo
