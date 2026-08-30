import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.CompilerChecker
import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.CompilerErasure
import Coercions.DOT.Captures.Acyclic.GeneralExpression.Examples

/-!
# Direct-compiler computational litmus

This module compiles the closed general-expression program whose function
position, object-producing right-hand side, selected function payload, and
argument all perform genuine computation.  It checks the emitted annotated
many-sorted FC artifact independently and records its non-administrative outer
shape.  The generic compiler-erasure theorem then transports the source's
six-step runtime trace to that independently checked artifact.
-/

namespace DOTCaptureToManySortedFC.Acyclic.GeneralExpression.ComputationalExample

namespace SourceExamples

export DOTCapture.Acyclic.GeneralExpression.Examples
  (selectComputedObject selectComputedObjectTyping computedObject
    computedProducer delayedUnit selectedApplication objectProducer
    selectComputedObject_erases_exactly selectComputedObjectSteps)

end SourceExamples

namespace Target

export ManySortedFC (Capture Ty Tm)

namespace Tm
export ManySortedFC.Tm (HasType IsValue check synth)
end Tm

end Target

abbrev emptyReady :=
  DOTCaptureToManySortedFC.Acyclic.RuntimeContext.nil

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
noncomputable abbrev selectComputedObject_compiles :
    (Compiler.compileTerm? emptyReady
      SourceExamples.selectComputedObjectTyping).isSome = true := by
  rfl

noncomputable abbrev compiled :=
  (Compiler.compileTerm? emptyReady
    SourceExamples.selectComputedObjectTyping).get
      selectComputedObject_compiles

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem selectComputedObject_compile_success :
    Compiler.compileTerm? emptyReady
        SourceExamples.selectComputedObjectTyping =
      some compiled := by
  rfl

theorem compiled_has_exact_target_indices :
    compiled.targetUse = (.empty : Target.Capture []) ∧
    compiled.targetType = (.one : Target.Ty []) := by
  constructor
  · apply Eq.symm
    apply Option.some.inj
    simpa [StaticTranslation.translateCapture?] using compiled.useTranslated
  · apply Eq.symm
    apply Option.some.inj
    simpa [StaticTranslation.translateTy?] using compiled.typeTranslated

noncomputable def compiled_is_well_typed :
    Target.Tm.HasType emptyReady.target compiled.term .empty .one := by
  simpa [compiled_has_exact_target_indices.1,
    compiled_has_exact_target_indices.2] using compiled.typing

theorem compiled_synthesizes_exact_indices :
    Target.Tm.synth emptyReady.target compiled.term =
      some ((.empty : Target.Capture []), (.one : Target.Ty [])) := by
  rw [← compiled_has_exact_target_indices.1,
    ← compiled_has_exact_target_indices.2]
  exact compiled.synthesizes_exactly

theorem compiled_checker_accepts :
    (Target.Tm.check emptyReady.target compiled.term).isSome = true :=
  compiled.checker_accepts

/-! ## Exact erasure and execution -/

theorem compiled_erases_exactly :
    compiled.term.erase =
      DOTCapture.Acyclic.GeneralExpression.Examples.Runtime.initial := by
  rw [CompilerErasure.compileTerm_erase
    selectComputedObject_compile_success]
  rfl

/-- The source's explicit six zeta/beta steps execute the compiled artifact
after target annotations, packages, and opens are erased. -/
def compiled_six_steps_to_unit :
    ManySortedFC.Runtime.Steps compiled.term.erase .unit := by
  apply (CompilerErasure.compileTerm_steps_iff
    selectComputedObject_compile_success).2
  exact SourceExamples.selectComputedObjectSteps

/-! ## Constructor-level target shape

The predicates ignore only explicit `Tm.use` annotations, which erase and do
not perform evaluation.  They do not skip ordinary target lets.  Thus the
result below says that the compiled artifact reaches `Tm.open` directly, its
package reaches `Tm.app` directly, and the application's function is a
computed let rather than a target value. -/

namespace TargetShape

/-- A genuine computed-let head, modulo runtime-transparent use annotations. -/
def HasLetHead {scope : ManySortedFC.Sig} : Target.Tm scope → Prop
  | .use term _ => HasLetHead term
  | .let' _ _ _ _ _ => True
  | _ => False

/-- A genuine application whose function has a computed-let head. -/
def IsComputedApplication {scope : ManySortedFC.Sig} :
    Target.Tm scope → Prop
  | .use term _ => IsComputedApplication term
  | .app function _ => HasLetHead function
  | _ => False

/-- An existential open whose package is the computed application above.
Only outer proof annotations may intervene; an ordinary temporary let cannot. -/
def IsDirectOpenOfComputedApplication {scope : ManySortedFC.Sig} :
    Target.Tm scope → Prop
  | .use term _ => IsDirectOpenOfComputedApplication term
  | .«open» _ _ _ _ package _ _ => IsComputedApplication package
  | _ => False

theorem hasLetHead_not_value {scope : ManySortedFC.Sig}
    {term : Target.Tm scope} (shape : HasLetHead term) :
    ¬ Target.Tm.IsValue term := by
  intro value
  cases value <;> simp_all [HasLetHead]

end TargetShape

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem compiled_is_direct_open_of_computed_application :
    TargetShape.IsDirectOpenOfComputedApplication compiled.term := by
  change True
  trivial

/-! ## Source/runtime nondegeneracy -/

structure SourceStats where
  lets : Nat
  lambdas : Nat
  applications : Nat
deriving DecidableEq

namespace SourceStats

def zero : SourceStats := ⟨0, 0, 0⟩

def add (left right : SourceStats) : SourceStats :=
  ⟨left.lets + right.lets,
    left.lambdas + right.lambdas,
    left.applications + right.applications⟩

def oneLet (stats : SourceStats) : SourceStats :=
  ⟨stats.lets + 1, stats.lambdas, stats.applications⟩

def oneLambda (stats : SourceStats) : SourceStats :=
  ⟨stats.lets, stats.lambdas + 1, stats.applications⟩

def oneApplication (stats : SourceStats) : SourceStats :=
  ⟨stats.lets, stats.lambdas, stats.applications + 1⟩

end SourceStats

mutual

def valueStats {scope : Nat} :
    DOTCapture.Acyclic.GeneralExpression.Value scope → SourceStats
  | .var _ => .zero
  | .unit => .zero
  | .lam _ _ body => (termStats body).oneLambda
  | .object _ _ _ payload => valueStats payload

def termStats {scope : Nat} :
    DOTCapture.Acyclic.GeneralExpression.Term scope → SourceStats
  | .ret value => valueStats value
  | .select _ _ => .zero
  | .app function argument =>
      ((termStats function).add (termStats argument)).oneApplication
  | .let' _ rhs body =>
      ((termStats rhs).add (termStats body)).oneLet

end

theorem source_has_computed_object_application :
    SourceExamples.computedObject =
      .app SourceExamples.computedProducer (.ret .unit) := by
  rfl

theorem source_has_delayed_argument :
    SourceExamples.delayedUnit =
      .let' .one (.ret .unit) (.ret (.var .here)) := by
  rfl

theorem source_has_exact_computational_spine :
    termStats SourceExamples.selectComputedObject = ⟨4, 2, 2⟩ := by
  rfl

theorem runtime_has_two_lambdas :
    DOTCapture.Acyclic.GeneralExpression.Examples.Runtime.lambdaCount
      DOTCapture.Acyclic.GeneralExpression.Examples.Runtime.initial = 2 :=
  DOTCapture.Acyclic.GeneralExpression.Examples.selectComputedObject_runtime_lambdaCount

theorem runtime_has_two_applications :
    DOTCapture.Acyclic.GeneralExpression.Examples.Runtime.applicationCount
      DOTCapture.Acyclic.GeneralExpression.Examples.Runtime.initial = 2 :=
  DOTCapture.Acyclic.GeneralExpression.Examples.selectComputedObject_runtime_applicationCount

theorem runtime_has_four_lets :
    DOTCapture.Acyclic.GeneralExpression.Examples.Runtime.letCount
      DOTCapture.Acyclic.GeneralExpression.Examples.Runtime.initial = 4 :=
  DOTCapture.Acyclic.GeneralExpression.Examples.selectComputedObject_runtime_letCount

theorem compiled_is_not_unit :
    compiled.term ≠ (.unit : Target.Tm []) := by
  intro equality
  have shape := compiled_is_direct_open_of_computed_application
  rw [equality] at shape
  exact shape

end DOTCaptureToManySortedFC.Acyclic.GeneralExpression.ComputationalExample
